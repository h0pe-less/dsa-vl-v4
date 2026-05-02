#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

// 128 bit cos products are getting big at high scale
typedef __int128_t int128;
// sample map space for optimal combinations
#define MAP_CAPACITY 2000000

// optimized (a^b) % mod using exponentiation by squaring
int64_t power_mod(int64_t base, int64_t exp, int64_t mod) {
    int64_t result = 1;
    base = base % mod;
    while (exp > 0) {
        if (exp % 2 == 1) {
            result = ((int128)result * base) % mod;
        }
        base = ((int128)base * base) % mod;
        exp /= 2;
    }
    return result;
}

// calculate modular inverse using Fermat Little Theorem
// using this to figure out what remainder are we missing to reach our target
int64_t mod_inverse(int64_t n, int64_t mod) {
    return power_mod(n, mod - 2, mod);
}

// custom print for int128 cos we can't print them by default
void print_int128(int128 n) {
    if (n == 0) {
        printf("0\n");
        return;
    }
    char buffer[128];
    int index = 0;
    while (n > 0) {
        buffer[index++] = (char)((n % 10) + '0');
        n /= 10;
    }
    while (index > 0) {
        putchar(buffer[--index]);
    }
    putchar('\n');
}


// map: remainder -> (weight, integer_product)
typedef struct {
    int64_t remainder;
    int weight;
    int128 product;
} MapEntry;

// initialize empty map
MapEntry* create_map() {
    MapEntry* map = calloc(MAP_CAPACITY, sizeof(MapEntry));
    for (int i = 0; i < MAP_CAPACITY; i++) {
        map[i].remainder = -1; // -1 means empty slot
    }
    return map;
}

// add entires to map if we find a cheaper way to get the remainder
void insert_or_update(MapEntry* map, int64_t rem, int weight, int128 prod) {
    uint64_t index = rem % MAP_CAPACITY;
    
    // linear probing, keep looking if the slot is taken by a different remainder
    while (map[index].remainder != -1 && map[index].remainder != rem) {
        index = (index + 1) % MAP_CAPACITY;
    }
    
    // update if its empty or we found a better/cheaper solution
    if (map[index].remainder == -1 || 
        weight < map[index].weight || 
       (weight == map[index].weight && prod < map[index].product)) {
        
        map[index].remainder = rem;
        map[index].weight = weight;
        map[index].product = prod;
    }
}

// recursively tries combinations of given primes up to the max_weight
void find_combinations(int prime_idx, int64_t current_rem, int128 current_prod, 
                       int current_weight, int max_weight, const int* primes, 
                       int num_primes, MapEntry* map, int64_t p) {
    
    // base case, if we looked at all primes in this group then save the result
    if (prime_idx == num_primes) {
        insert_or_update(map, current_rem, current_weight, current_prod);
        return;
    }

    int prime = primes[prime_idx];
    // cost of using prime 'p' is (p-1) because we need to pair it with 1 to get p-1 mod p
    int prime_weight = prime - 1; 
    
    // claculate how many times can we multiply this prime before we exceed max_weight
    int max_exponent = (max_weight - current_weight) / prime_weight;

    int64_t rem = current_rem;
    int128 prod = current_prod;
    int weight = current_weight;

    // trying to use this prime 0,1,2 ... times
    for (int exponent = 0; exponent <= max_exponent; exponent++) {
        find_combinations(prime_idx + 1, rem, prod, weight, max_weight, primes, num_primes, map, p);
        rem = ((int128)rem * prime) % p;
        prod *= prime;
        weight += prime_weight;
    }
}

typedef struct {
    int weight;
    int64_t remainder;
    int128 product;
    int64_t inv_remainder; // inversed remainder for quick calculations ( formula )
} State;

// sort helper for qsort (by weight ascending)
int compare_states(const void *a, const void *b) {
    return ((State*)a)->weight - ((State*)b)->weight;
}

// find minimal cost product within a bound
int128 search_with_bound(int64_t p, int max_weight) {
     
    // grouping primes into a(small) and b(large) primes for future calculations
    int primes_a[] = {5, 7, 11, 13, 17, 19, 23};
    int num_primes_a = 7;
    
    int primes_b[200]; 
    int num_primes_b = 0;
    
    // using sieve to find primes >= 29 up to max_weight
    for (int i = 29; i <= max_weight + 1; i++) {
        int is_prime = 1;
        for (int j = 2; j * j <= i; j++) {
            if (i % j == 0) {
                is_prime = 0;
                break;
            }
        }
        if (is_prime) primes_b[num_primes_b++] = i;
    }

    // generate maps for both groups of primes
    MapEntry* map_a = create_map();
    MapEntry* map_b = create_map();

    find_combinations(0, 1, 1, 0, max_weight, primes_a, num_primes_a, map_a, p);
    find_combinations(0, 1, 1, 0, max_weight, primes_b, num_primes_b, map_b, p);

    // building states for group c (2s and 3s) since they are common and constantly used
    State* states_23 = malloc(20000 * sizeof(State));
    int count_23 = 0;
    
    for (int exp3 = 0; exp3 <= max_weight / 2; exp3++) {
        for (int exp2 = 0; exp2 <= (max_weight - 2 * exp3); exp2++) {
            int weight = (2 * exp3) + exp2;
            int128 prod = 1;
            int64_t rem = 1;
            
            for(int i = 0; i < exp3; i++) { prod *= 3; rem = (rem * 3) % p; }
            for(int i = 0; i < exp2; i++) { prod *= 2; rem = (rem * 2) % p; }
            
            states_23[count_23++] = (State){weight, rem, prod, mod_inverse(rem, p)};
        }
    }
    qsort(states_23, count_23, sizeof(State), compare_states);

    // transform map b into an array for easier iteration
    State* states_b = malloc(MAP_CAPACITY * sizeof(State));
    int count_b = 0;
    for (int i = 0; i < MAP_CAPACITY; i++) {
        if (map_b[i].remainder != -1) {
            states_b[count_b++] = (State){
                map_b[i].weight, 
                map_b[i].remainder, 
                map_b[i].product, 
                mod_inverse(map_b[i].remainder, p)
            };
        }
    }
    qsort(states_b, count_b, sizeof(State), compare_states);

    // using "meet in the middle" strategy to find optimal combinations of states from b and c groups
    int best_weight_found = 1000000000;
    int128 best_product_found = -1;
    
    // by Wilson Theorem, our total product must equal -1 mod p = p - 1
    int64_t target_remainder = p - 1;

    for (int i = 0; i < count_b; i++) {
        int remaining_weight = max_weight - states_b[i].weight;
        
        // knwing the remainder of B, calculate what we need from A and C to hit our target
        // Target = (Rem B * Rem C * Rem A) % p
        // Hence, (Rem C * Rem A) needs to equal (Target / Rem B) % p
        int64_t needed_from_23_and_A = ((int128)target_remainder * states_b[i].inv_remainder) % p;

        for (int j = 0; j < count_23; j++) {
            // stop if we exceed the weight limit for group C
            if (states_23[j].weight > remaining_weight) break;
            
            // Rem A = (needed_from_23_and_A / Rem 23) % p
            int64_t exactly_needed_from_a = ((int128)needed_from_23_and_A * states_23[j].inv_remainder) % p;
            
            // look up in map A for the needed remainder
            uint64_t index = exactly_needed_from_a % MAP_CAPACITY;
            while (map_a[index].remainder != -1 && map_a[index].remainder != exactly_needed_from_a) {
                index = (index + 1) % MAP_CAPACITY;
            }
            
            // if we found a matching in A map then we have a valid combination
            if (map_a[index].remainder != -1) {
                int total_weight = states_b[i].weight + states_23[j].weight + map_a[index].weight;
                
                if (total_weight <= max_weight) {
                    int128 total_product = states_b[i].product * states_23[j].product * map_a[index].product;
                    
                    // update the best solution if we found a better one
                    if (total_weight < best_weight_found) { 
                        best_weight_found = total_weight; 
                        best_product_found = total_product; 
                    }
                    else if (total_weight == best_weight_found && (best_product_found == -1 || total_product < best_product_found)) {
                        best_product_found = total_product;
                    }
                }
            }
        }
    }
    
    free(states_23); 
    free(states_b); 
    free(map_a); 
    free(map_b);
    
    return best_product_found;
}

int main() {
    int64_t p;
    printf("Enter p: ");
    scanf("%lld", &p);
    
    // starting from a low max weight, then increase it if no solutions were found
    int current_max_weight = 240; 
    
    while (1) {
        int128 result = search_with_bound(p, current_max_weight);
        
        if (result != -1) {
            printf("Answer for p = %lld: ", p);
            print_int128(result); 
            break; 
        }
        
        // increase the limit if nothing was found
        current_max_weight += 20;
    }
    
    return 0;
}