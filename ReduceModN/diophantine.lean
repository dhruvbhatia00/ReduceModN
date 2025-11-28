import Mathlib

/--
Over `ZMod 4`, every square is either 0 or 1. We package it in a form
we can use later; `by decide` checks the finite cases automatically.
-/
lemma zmod4_sq_is_zero_or_one : ∀ a : ZMod 4, a^2 = 0 ∨ a^2 = 1 := by
  decide

/-- Over `ZMod 4`, a sum of two squares can never be 3. -/
lemma zmod4_sum_of_squares_ne_three : ∀ a b : ZMod 4, a^2 + b^2 ≠ 3 := by
  -- Finite check: 16 cases (a,b) ∈ (ZMod 4)^2
  decide

/--
There are no integer solutions to `x^2 + y^2 = 3`.
We reduce the equation modulo 4 and contradict the finite check above.
-/
theorem no_int_solutions_x2_add_y2_eq_three :
  ¬ ∃ x y : ℤ, x^2 + y^2 = 3 := by
  rintro ⟨x, y, hxy⟩
  -- Reduce both sides modulo 4
  have hmod : (x : ZMod 4)^2 + (y : ZMod 4)^2 = (3 : ZMod 4) := by
    -- cast the equality to ZMod 4 and use that casts preserve + and ^
    have h1 := congrArg (Int.cast : ℤ → ZMod 4) hxy
    push_cast at h1
    exact h1
  -- But sums of two squares in ZMod 4 are never 3
  have hne : (x : ZMod 4)^2 + (y : ZMod 4)^2 ≠ (3 : ZMod 4) := by
    exact zmod4_sum_of_squares_ne_three (x : ZMod 4) (y : ZMod 4)
  exact hne hmod


-- Helper lemma: rewriting a rational number in terms of its numerator and denominator
theorem ratsimplify : ∀ (x: ℚ), x.den * x = x.num := by
  exact fun x => Rat.den_mul_eq_num x

-- Some lemmas about squares modulo 4 for later use
lemma mul_four_add_one : ∀ k : ℤ, (4 * k + 1 : ZMod 4) = 1 := by
  intro k
  have hk : ((4 * k : ℤ) : ZMod 4) = 0 := by
    simp [show (4 : ZMod 4) = 0 by decide]
  push_cast at hk
  rw [hk]
  simp
-- Lemma: if n is even, then n^2 ≡ 0 (mod 4)
lemma evensquaremodfour : ∀ n : ℤ, Even n → (n ^ 2 : ZMod 4) = 0 := by
    intro n hn
    rcases hn with ⟨k, rfl⟩
    norm_cast
    ring_nf
    simp [show (4 : ZMod 4) = 0 by decide]
-- Lemma: if n^2 ≡ 0 (mod 4), then n is even
lemma sqmodfourzero_implies_even : ∀ n : ℤ, (n ^ 2 : ZMod 4) = 0 → Even n := by
  intro n hn
  -- Prove by contrapositive: if n is odd, then n^2 ≡ 1 (mod 4)
  refine (Int.even_or_odd n).resolve_right ?_
  intro hodd
  obtain ⟨k, hk⟩ := hodd
  have hk_sq_int : n ^ 2 = 4 * (k ^ 2 + k) + 1 := by
    have : (2 * k + 1 : ℤ) ^ 2 = 4 * (k ^ 2 + k) + 1 := by
      ring
    simpa [hk] using this
  have hk_sq : (n : ZMod 4) ^ 2 = 1 := by
    have := congrArg (fun t : ℤ => (t : ZMod 4)) hk_sq_int
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow] at this
    rw [this]
    push_cast
    convert mul_four_add_one (k ^ 2 + k) using 2
    simp [mul_comm]
  have : (0 : ZMod 4) = 1 := by simpa [hn] using hk_sq
  exact absurd this (by decide : (0 : ZMod 4) ≠ 1)

-- Lemma: if a^2 + b^2 ≡ 0 (mod 4), then a^2 ≡ 0 (mod 4) and b^2 ≡ 0 (mod 4)
lemma sum_zeromodfour_implies_both_zero_modfour :
  ∀ a b : ZMod 4, a ^ 2 + b ^ 2 = 0 → a ^ 2 = 0 ∧ b ^ 2 = 0 := by
  intro a b hab
  have ha : a ^ 2 = 0 ∨ a ^ 2 = 1 := zmod4_sq_is_zero_or_one a
  have hb : b ^ 2 = 0 ∨ b ^ 2 = 1 := zmod4_sq_is_zero_or_one b
  rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1
  · exact ⟨ha0, hb0⟩
  · rw [ha0, hb1] at hab; exact absurd hab (by decide : (1 : ZMod 4) ≠ 0)
  · rw [ha1, hb0] at hab; exact absurd hab (by decide : (1 : ZMod 4) ≠ 0)
  · rw [ha1, hb1] at hab; exact absurd hab (by decide : (2 : ZMod 4) ≠ 0)

-- Lemma: the numerator and denominator of a rational number are coprime
lemma numanddenom_coprime : ∀ x : ℚ, Int.gcd x.num x.den = 1 := by
  intro x
  exact x.reduced
-- Lemma: if 2 divides both a and b, then 2 divides gcd(a,b) -/
lemma twodividesa_twodividesb_twodividesgcd :
  ∀ a b : ℤ, (2 : ℤ) ∣ a → (2 : ℤ) ∣ b → (2 : ℤ) ∣ Int.gcd a b := by
  intro a b ha hb
  exact Int.dvd_gcd ha hb

-- divisibility lemmas for numerator and denominator of rationals
  lemma twodividenum_thentwodoesntdivdenom :
    ∀ x : ℚ, (2 : ℤ) ∣ x.num → ¬ (2 : ℤ) ∣ x.den := by
    intro x hnumdiv hdendiv
    have h_gcd := numanddenom_coprime x
    have h_gcd_div := twodividesa_twodividesb_twodividesgcd x.num x.den hnumdiv hdendiv
    have : (2 : ℤ) ∣ 1 := by
      rw [h_gcd] at h_gcd_div
      exact h_gcd_div
    exact absurd this (by decide : ¬ (2 : ℤ) ∣ 1)

  lemma twodividenom_thentwodoesntdivnum :
    ∀ x : ℚ, (2 : ℤ) ∣ x.den → ¬ (2 : ℤ) ∣ x.num := by
    intro x hdendiv hnumdiv
    have h_gcd := numanddenom_coprime x
    have h_gcd_div := twodividesa_twodividesb_twodividesgcd x.num x.den hnumdiv hdendiv
    have : (2 : ℤ) ∣ 1 := by
      rw [h_gcd] at h_gcd_div
      exact h_gcd_div
    exact absurd this (by decide : ¬ (2 : ℤ) ∣ 1)

def gcd3integer (a b c : ℤ) : ℤ :=
  Int.gcd (Int.gcd a b) c
-- Lemma: gcd of two integers divides both integers
lemma gcdof2integers_dvd_both :
  ∀ (a b : ℤ), let d := Int.gcd a b
  (d : ℤ) ∣ a ∧ (d : ℤ) ∣ b := by
  intros a b
  exact ⟨Int.gcd_dvd_left, Int.gcd_dvd_right⟩

-- Lemma: gcd3integer divides all three integers a,b,c
lemma gcd3integer_dvd_all :
  ∀ (a b c : ℤ), let d := gcd3integer a b c
  d ∣ a ∧ d ∣ b ∧ d ∣ c := by
  intros a b c
  classical
  let gab : ℤ := (Int.gcd a b : ℤ)
  let d := gcd3integer a b c
  have hgab_a : gab ∣ a := by
    simpa [gab] using (Int.gcd_dvd_left : (Int.gcd a b : ℤ) ∣ a)
  have hgab_b : gab ∣ b := by
    simpa [gab] using (Int.gcd_dvd_right : (Int.gcd a b : ℤ) ∣ b)
  have hd_gab : d ∣ gab := by
    simpa [d, gab, gcd3integer] using
      (Int.gcd_dvd_left : (Int.gcd (Int.gcd a b) c : ℤ) ∣ Int.gcd a b)
  have hd_c : d ∣ c := by
    simpa [d, gcd3integer] using
      (Int.gcd_dvd_right : (Int.gcd (Int.gcd a b) c : ℤ) ∣ c)
  exact ⟨Int.dvd_trans hd_gab hgab_a, Int.dvd_trans hd_gab hgab_b, hd_c⟩

-- Lemma: from a^2 = b^2, we can derive (a/d)^2 = (b/d)^2 where d = gcd(a,b)
lemma asqeqbsq_implies_abydsqeqbbydsq_wheredisgcd :
  ∀ (a b : ℤ), a^2 = b^2 →
    let d := Int.gcd a b
    (a / d)^2 = (b / d)^2 := by
  sorry
 -- Lemma: from a solution to a^2 + b^2 = 3 c^2, we can derive a smaller solution
lemma ifabcsolution_thennewsolutionbydividinggcd3 :
  ∀ (a b c : ℤ), a^2 + b^2 = 3*c^2 →
    let d := gcd3integer a b c
    (a / d)^2 + (b / d)^2 =3* (c / d)^2 := by
  intros a b c h_eq
  let d := gcd3integer a b c
  sorry


  -- Lemma: dividing a,b,c by their gcd3 makes them primitive (no common factor >1)
lemma dividingby3numbersbygcd_makesprimitive :
    ∀ (a b c : ℤ),
      let d := gcd3integer a b c
      ¬ ∃ k : ℤ, k > 1 ∧ k ∣ (a / d) ∧ k ∣ (b / d) ∧ k ∣ (c / d) := by
    intros a b c
    let d := gcd3integer a b c
    sorry


-- Lemma: from a^2 + b^2 = 3 c^2, c must be even
lemma asqplusbsq_eq_threecsq_impliesceven :
  ∀ a b c : ℤ, a^2 + b^2 = 3 * c^2 → Even c := by
  intro a b c h_eq
  classical
  have hmod :
      (a : ZMod 4) ^ 2 + (b : ZMod 4) ^ 2 = (3 : ZMod 4) * (c : ZMod 4) ^ 2 := by
    have := congrArg (fun t : ℤ => (t : ZMod 4)) h_eq
    simpa [pow_two] using this
  have hsum := zmod4_sum_of_squares_ne_three (a : ZMod 4) (b : ZMod 4)
  have hc_sq_zero : (c : ZMod 4) ^ 2 = 0 := by
    rcases zmod4_sq_is_zero_or_one (c : ZMod 4) with hc0 | hc1
    · exact hc0
    · exact (hsum (by simpa [hc1, mul_comm, mul_left_comm, mul_assoc] using hmod)).elim
  exact sqmodfourzero_implies_even c hc_sq_zero

-- Lemma: from a^2 + b^2 = 3 c^2, a and b must be even
lemma asqplusbsq_eq_threecsq_impliesaandbeven :
  ∀ a b c : ℤ, a^2 + b^2 = 3 * c^2 →
    Even a ∧ Even b := by
  intro a b c h_eq
  classical
  have hmod :
      (a : ZMod 4) ^ 2 + (b : ZMod 4) ^ 2 = (3 : ZMod 4) * (c : ZMod 4) ^ 2 := by
    have := congrArg (fun t : ℤ => (t : ZMod 4)) h_eq
    simpa [pow_two] using this
  have hsum := zmod4_sum_of_squares_ne_three (a : ZMod 4) (b : ZMod 4)
  have hc_sq_zero : (c : ZMod 4) ^ 2 = 0 := by
    rcases zmod4_sq_is_zero_or_one (c : ZMod 4) with hc0 | hc1
    · exact hc0
    · exact (hsum (by simpa [hc1, mul_comm, mul_left_comm, mul_assoc] using hmod)).elim
  rw [hc_sq_zero] at hmod
  simp at hmod
  have asqzero_bsqzero : (a : ZMod 4) ^ 2 = 0 ∧ (b : ZMod 4) ^ 2 = 0 := by
    exact sum_zeromodfour_implies_both_zero_modfour (a : ZMod 4) (b : ZMod 4) hmod
  rcases asqzero_bsqzero with ⟨ha_sq_zero, hb_sq_zero⟩
  exact ⟨sqmodfourzero_implies_even a ha_sq_zero,
         sqmodfourzero_implies_even b hb_sq_zero⟩


/--
There are no rational solutions to `x^2 + y^2 = 3`.
We use a common denominator and reducedness of `Rat`.
-/
theorem no_rat_solutions_x2_add_y2_eq_three :
  ¬ ∃ x y : ℚ, x^2 + y^2 = 3 := by
  classical
  rintro ⟨x, y, hxy⟩
  -- Common denominator d = x.den * y.den
  set d : ℤ := x.den * y.den with hd
  have hd_pos : 0 < d := by
    have hxpos : (0 : ℤ) < x.den := Int.ofNat_pos.mpr x.pos
    have hypos : (0 : ℤ) < y.den := Int.ofNat_pos.mpr y.pos
    simpa [hd] using mul_pos hxpos hypos

  -- Numerators corresponding to the common denominator
  set p : ℤ := x.num * y.den with hp
  set q : ℤ := y.num * x.den with hq

  -- Step 1: clear denominators to get an integer equation p^2 + q^2 = 3 d^2
  have hInt : p^2 + q^2 = 3 * d^2 := by
    -- Express numerators via the rationals x and y.
    have hx_repr : (x.num : ℚ) = (x.den : ℚ) * x := by
      exact (ratsimplify x).symm
    have hy_repr : (y.num : ℚ) = (y.den : ℚ) * y := by
      exact (ratsimplify y).symm
    -- Rewrite p and q using the common denominator d.
    have hp_repr : (p : ℚ) = (d : ℚ) * x := by
      rw [hp, hd]
      push_cast
      rw [hx_repr]
      ring
    have hq_repr : (q : ℚ) = (d : ℚ) * y := by
      rw [hq, hd]
      push_cast
      rw [hy_repr]
      ring
    -- Substitute into the equation x^2 + y^2 = 3 and clear the factor (d : ℚ)^2.
    have hQ : (p : ℚ) ^ 2 + (q : ℚ) ^ 2 = 3 * (d : ℚ) ^ 2 := by
      rw [hp_repr, hq_repr]
      rw [mul_pow, mul_pow]
      rw [← hxy]
      ring
    -- Cast back down to ℤ
    have hQ' : ((p ^ 2 + q ^ 2 : ℤ) : ℚ) = (3 * d ^ 2 : ℤ) := by
      simpa [pow_two] using hQ
    exact Int.cast_injective hQ'

  -- Step 2: descend to a primitive integer solution and contradict evenness
  have : False := by
    -- helper lemmas will produce the desired contradiction
    set g := gcd3integer p q d with hg
    have h_reduced :
        (p / g) ^ 2 + (q / g) ^ 2 = 3 * (d / g) ^ 2 := by
      simpa [g] using ifabcsolution_thennewsolutionbydividinggcd3 p q d hInt
    have h_primitive :
        ¬ ∃ k : ℤ, k > 1 ∧ k ∣ (p / g) ∧ k ∣ (q / g) ∧ k ∣ (d / g) := by
      simpa [g] using dividingby3numbersbygcd_makesprimitive p q d
    have h_even_c' : Even (d / g) :=
      asqplusbsq_eq_threecsq_impliesceven (p / g) (q / g) (d / g) h_reduced
    have h_even_a'b' :=
      asqplusbsq_eq_threecsq_impliesaandbeven (p / g) (q / g) (d / g) h_reduced
    have h_even_a' : Even (p / g) := h_even_a'b'.1
    have h_even_b' : Even (q / g) := h_even_a'b'.2
    have h_two_div_a' : (2 : ℤ) ∣ (p / g) := by
      rcases h_even_a' with ⟨k₁, hk₁⟩
      exact ⟨k₁, by rw [two_mul]; exact hk₁⟩
    have h_two_div_b' : (2 : ℤ) ∣ (q / g) := by
      rcases h_even_b' with ⟨k₂, hk₂⟩
      exact ⟨k₂, by rw [two_mul]; exact hk₂⟩
    have h_two_div_c' : (2 : ℤ) ∣ (d / g) := by
      rcases h_even_c' with ⟨k₃, hk₃⟩
      exact ⟨k₃, by rw [two_mul]; exact hk₃⟩
    exact h_primitive ⟨2, by decide, h_two_div_a', h_two_div_b', h_two_div_c'⟩

  exact this
