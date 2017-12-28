package word

import (
	"math/rand"
	"testing"
	"time"
)

func TestPalindrome(t *testing.T) {
	if !IsPalindrome("detartrated") {
		t.Error(`IsPalindrome("detartrated") = false`)
	}
	if !IsPalindrome("kayak") {
		t.Error(`IsPalindrome("kayak") = false`)
	}
}

func TestNonPalindrome(t *testing.T) {
	if IsPalindrome("palindrome") {
		t.Error(`IsPalindrome("palindrome") = true`)
	}
}

func TestFrenchPalindrome(t *testing.T) {
	if !IsPalindrome("été") {
		t.Error(`IsPalindrome("été") = false`)
	}
}

func TestCanalPalindrome(t *testing.T) {
	input := "A man, a plan, a canal: Panama"
	if !IsPalindrome(input) {
		t.Errorf(`IsPalindrome(%q) = false`, input)
	}
}

func TestTableDrivenPalindrome(t *testing.T){
	table := [] struct{
		input string
		want bool
	}{
		{"", true},
		{"a", true},
		{"aa", true},
		{"ab", false},
		{"kayak", true},
		{"detartrated", true},
		{"A man, a plan, a canal: Panama", true},
		{"Evil I did dwell; lewd did I live.", true},
		{"Able was I ere I saw Elba", true},
		{"été", true},
		{"Et se resservir, ivresse reste.", true},
		{"palindrome", false}, // non-palindrome
		{"desserts", false}, // semi-palindrome
	}

	for _, test := range table{
		if IsPalindrome(test.input) != test.want{
			t.Errorf(`IsPalindrome(%q) = %v`, test.input, test.want)
		}
	}
}

func randomPalindrome(rn *rand.Rand) string {
	n := rn.Intn(25)
	runes := make([]rune, n)
	for i := 0; i < (n+1)/2; i++ {
		r := rune(rn.Intn(0x1000))
		runes[i] = r
		runes[n - i - 1] = r
	}
	return string(runes)
}

func TestRandomPalindromes(t *testing.T) {
	seed := time.Now().UTC().UnixNano()
	rn := rand.New(rand.NewSource(seed))
	input := randomPalindrome(rn)
	for i:=0; i< 1000; i++ {
		if !IsPalindrome(input) {
			t.Errorf(`IsPalindrome(%q) = false`, input)
		}
	}
}

func BenchmarkCanalPalindrome(b *testing.B) {
	for i:=0; i< b.N; i++{
		IsPalindrome("A man, a plan, a canal: Panama")
	}
}
