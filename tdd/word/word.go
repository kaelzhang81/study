package word

import "unicode"

func IsPalindrome(word string) bool {
	var letters []rune
	for _, s := range word{
		if unicode.IsLetter(s){
			letters = append(letters, unicode.ToLower(s))
		}
	}
	for i := range letters {
		if letters[i] != letters[len(letters)-i-1] {
			return false
		}
	}
	return true
}
