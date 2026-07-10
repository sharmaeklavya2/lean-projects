module

@[expose] public section

def syl : Nat → Nat
  -- https://oeis.org/A007018
  -- Sylvester's sequence minus 1
  | 0 => 0
  | 1 => 1
  | n + 1 => syl n * (syl n + 1)

theorem syl_pos (n : Nat) : 1 ≤ syl (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    -- syl (k+2) = syl (k+1) * (syl (k+1) + 1) ≥ syl (k+1) ≥ 1
    change 1 ≤ syl (k + 1) * (syl (k + 1) + 1)
    exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

theorem syl_inc (n : Nat) : syl n + 1 ≤ syl (n + 1) := by
  match n with
  | 0 => decide
  | k + 1 =>
    have h : 1 ≤ syl (k + 1) := syl_pos k
    -- syl (k+2) = syl (k+1) * (syl (k+1) + 1); the increment costs
    -- (syl (k+1) - 1) * (syl (k+1) + 1) ≥ 0 since syl (k+1) ≥ 1
    change syl (k + 1) + 1 ≤ syl (k + 1) * (syl (k + 1) + 1)
    exact Nat.le_mul_of_pos_left _ h

-- `syl` is (weakly) monotone: derived from the strict step `syl_inc`.
theorem syl_le {a b : Nat} (h : a ≤ b) : syl a ≤ syl b := by
  induction b with
  | zero =>
    have : a = 0 := Nat.le_zero.mp h
    subst this; exact Nat.le_refl _
  | succ n ih =>
    by_cases hn : a ≤ n
    · have h1 := ih hn
      have h2 := syl_inc n
      omega
    · have : a = n + 1 := by omega
      subst this; exact Nat.le_refl _

-- Strict monotonicity: `a < b → syl a < syl b`.
theorem syl_lt {a b : Nat} (h : a < b) : syl a < syl b := by
  have h1 := syl_le (a := a + 1) (b := b) h
  have h2 := syl_inc a
  omega

def syl_inv_slow : Nat → Nat
  | 0 => 0
  | M + 1 =>
    let j := syl_inv_slow M
    if M + 1 ≤ syl j then j else j + 1

-- Forward direction: `syl_inv_slow M` is *a* least index `i` with `M ≤ syl i`.
theorem syl_inv_slow_spec (M : Nat) :
    M ≤ syl (syl_inv_slow M) ∧ (∀ j < syl_inv_slow M, syl j < M) := by
  induction M with
  | zero =>
    refine ⟨by decide, ?_⟩
    intro j hj
    simp only [syl_inv_slow] at hj          -- syl_inv_slow 0 = 0, so j < 0 is impossible
    exact absurd hj (Nat.not_lt_zero j)
  | succ n hn =>
    obtain ⟨ih1, ih2⟩ := hn
    simp only [syl_inv_slow]
    split
    · next hc =>          -- hc : n + 1 ≤ syl (syl_inv_slow n); answer stays at j₀
      exact ⟨hc, fun j hj => Nat.lt_succ_of_lt (ih2 j hj)⟩
    · next hc =>          -- hc : ¬ (n + 1 ≤ syl (syl_inv_slow n)); answer steps to j₀ + 1
      simp only [Nat.not_le] at hc          -- syl (syl_inv_slow n) < n + 1
      have hstep := syl_inc (syl_inv_slow n)  -- syl j₀ + 1 ≤ syl (j₀ + 1)
      refine ⟨by omega, ?_⟩                   -- n + 1 ≤ syl (j₀+1) from ih1 : n ≤ syl j₀
      intro j hj
      have hle : j ≤ syl_inv_slow n := Nat.lt_succ_iff.mp hj
      rcases Nat.eq_or_lt_of_le hle with h | h
      · subst h; exact hc                     -- j = j₀: syl j₀ < n + 1
      · exact Nat.lt_succ_of_lt (ih2 j h)     -- j < j₀: syl j < n < n + 1

-- The predicate "least index with `M ≤ syl ·`" pins down `i` uniquely, so it
-- characterizes `syl_inv_slow M` exactly.
theorem syl_inv_slow_correct (M i : Nat)
    : i = syl_inv_slow M ↔ M ≤ syl i ∧ (∀ j < i, syl j < M) := by
  constructor
  · rintro rfl
    exact syl_inv_slow_spec M
  · rintro ⟨h1, h2⟩
    obtain ⟨s1, s2⟩ := syl_inv_slow_spec M
    -- uniqueness by trichotomy: a strictly smaller index would break `M ≤ syl ·`
    rcases Nat.lt_trichotomy i (syl_inv_slow M) with h | h | h
    · exact absurd h1 (Nat.not_le.mpr (s2 i h))   -- i < s ⇒ syl i < M, contra M ≤ syl i
    · exact h
    · exact absurd s1 (Nat.not_le.mpr (h2 _ h))   -- s < i ⇒ syl s < M, contra M ≤ syl s

def syl_inv_fast_helper (j M : Nat) : Nat :=
  -- find smallest i ≥ j such that M ≤ syl i
  if hMcomp: M ≤ syl j
  then j
  else syl_inv_fast_helper (j+1) M
termination_by M - syl j
decreasing_by
  have hinc := syl_inc j
  omega

def syl_inv_fast : Nat → Nat := syl_inv_fast_helper 0

-- #eval syl_inv_fast (syl 10)

-- Forward spec for the helper, proved by its *own* well-founded induction
-- principle (recursion on `j`, with `M` fixed). The precondition `hj` — that
-- every index below the current lower bound `j` already falls short of `M` — is
-- carried through the motive and re-established at each step.
theorem syl_inv_fast_helper_spec (M j : Nat) (hj : ∀ k < j, syl k < M) :
    M ≤ syl (syl_inv_fast_helper j M) ∧ (∀ k < syl_inv_fast_helper j M, syl k < M) := by
  induction j using syl_inv_fast_helper.induct (M := M) with
  | case1 x hle =>          -- found: M ≤ syl x, so helper returns x
    rw [syl_inv_fast_helper.eq_def, dif_pos hle]
    exact ⟨hle, hj⟩
  | case2 x hgt ih =>       -- step: ¬ M ≤ syl x, recurse at x+1
    rw [syl_inv_fast_helper.eq_def, dif_neg hgt]
    apply ih
    intro k hk
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with h | h
    · subst h; exact Nat.not_le.mp hgt   -- k = x: syl x < M from ¬ M ≤ syl x
    · exact hj k h                        -- k < x: from the old lower bound

theorem syl_inv_fast_spec (M : Nat) :
    M ≤ syl (syl_inv_fast M) ∧ (∀ j < syl_inv_fast M, syl j < M) :=
  -- start from j = 0; the lower bound `∀ k < 0, …` is vacuous
  syl_inv_fast_helper_spec M 0 (fun k hk => absurd hk (Nat.not_lt_zero k))

-- Same characterization as the slow version — the least index is unique.
theorem syl_inv_fast_correct (M i : Nat)
    : i = syl_inv_fast M ↔ M ≤ syl i ∧ (∀ j < i, syl j < M) := by
  constructor
  · rintro rfl
    exact syl_inv_fast_spec M
  · rintro ⟨h1, h2⟩
    obtain ⟨s1, s2⟩ := syl_inv_fast_spec M
    rcases Nat.lt_trichotomy i (syl_inv_fast M) with h | h | h
    · exact absurd h1 (Nat.not_le.mpr (s2 i h))
    · exact h
    · exact absurd s1 (Nat.not_le.mpr (h2 _ h))

-- Equivalence of the two implementations, for free from the two iff specs:
-- `syl_inv_fast M` satisfies the predicate that uniquely characterizes
-- `syl_inv_slow M`.
theorem syl_inv_fast_eq_slow (M : Nat) : syl_inv_fast M = syl_inv_slow M :=
  (syl_inv_slow_correct M (syl_inv_fast M)).mpr (syl_inv_fast_spec M)
