import Mathlib.Data.Real.Basic


def Function.convergesTo (s : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |s n - l| < ε

lemma add_convergesTo {u v : ℕ → ℝ} {a b : ℝ}
    (hu : u.convergesTo a) (hv : v.convergesTo b) :
    (u + v).convergesTo (a + b) := by
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
    (hu : u.convergesTo a) (hv : v.convergesTo b) (hw : w.convergesTo c) :
    (u + v + w).convergesTo (a + b + c) := by
  apply add_convergesTo
  apply add_convergesTo
  exact hu
  exact hv
  exact hw
