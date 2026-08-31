namespace CN_Lib

def wrapI (minInt : Int) (maxInt : Int) x :=
  let delta := ((maxInt - minInt) + 1)
  let r := x % delta
  (if (r <= maxInt) then r else r - delta)

theorem dvd_mod_minus (a b c : Int):
  (0 ≤ c) ∧ (c < b) → (b ∣ a - c) → a % b = c :=
by
  rintro ⟨hc0, hcb⟩ ⟨k, hk⟩
  have ha : a = c + b * k := by omega
  simp [ha, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hc0 hcb]

theorem wrapI_idem:
  ∀ (minInt maxInt x : Int),
  (minInt ≤ x ∧ x ≤ maxInt) →
  (minInt ≤ 0 ∧ 0 < maxInt) →
  wrapI minInt maxInt x = x :=
by
  intros minInt maxInt x H1 H2
  unfold wrapI
  let delta := ((maxInt - minInt) + 1)
  by_cases hx : 0 ≤ x
  · simp
    rw [Int.emod_eq_of_lt]
    omega; exact hx ;omega
  · simp
    rw [dvd_mod_minus _ _ (x + delta)]
    · by_cases hx' : (x + delta <= maxInt)
      · omega
      · omega
    · omega
    · exists (-1); omega
