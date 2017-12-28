package word

func IsPalindrome(word string) bool {
	letters := []rune(word)
	for i := range letters {
		if letters[i] != letters[len(letters)-i-1] {
			return false
		}
	}
	return true
}
