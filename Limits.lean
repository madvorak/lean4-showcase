import Mathlib.Data.Real.Basic


def Function.tendsTo (s : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - l| < ε

@[simp]
lemma seq_add_tendsTo {u v : ℕ → ℝ} {a b : ℝ}
    (hu : u.tendsTo a) (hv : v.tendsTo b) :
    (u + v).tendsTo (a + b) := by
  intro ε epp
  obtain ⟨Nᵤ, ha⟩ := hu (ε / 2) (half_pos epp)
  obtain ⟨Nᵥ, hb⟩ := hv (ε / 2) (half_pos epp)
  use max Nᵤ Nᵥ
  intro n hn
  specialize ha n (le_of_max_le_left hn)
  specialize hb n (le_of_max_le_right hn)
  calc |(u n + v n) - (a + b)|
    = |(u n - a) + (v n - b)| := by ring_nf
  _ ≤ |u n - a| + |v n - b|   := abs_add (u n - a) (v n - b)
  _ < ε / 2 + ε / 2           := add_lt_add ha hb
  _ = ε                       := add_halves ε

example {u v w : ℕ → ℝ} {a b c : ℝ}
    (hu : u.tendsTo a) (hv : v.tendsTo b) (hw : w.tendsTo c) :
    (u + v + w).tendsTo (a + b + c) := by
  aesop
