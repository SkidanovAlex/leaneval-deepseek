import Mathlib
import Submission.Work.WilE4.Poly.spec_pderiv

namespace Work.WilE4.CAD

open Polynomial

/-- Among the members of a finite family of polynomials that is closed under differentiation in
the last variable, and all of whose specialisations `spec (P i) x₀` are non-zero at a point `t₀`
that is a root of at least one of them, there is one whose specialisation has a root of
multiplicity exactly one at `t₀`.

Indeed, if `p = spec (P i) x₀` is non-zero and vanishes at `t₀` with multiplicity `n ≥ 2`, then
its derivative `spec (P j) x₀ = p.derivative` (where `P j = ∂/∂Xₘ (P i)`) is again non-zero and
vanishes at `t₀`, with multiplicity `n - 1`.  Iterating along the closure of the family therefore
reaches multiplicity one, which is the least possible value; taking a member of minimal
multiplicity gives the claim. -/
theorem exists_minimal_rootMultiplicity_member {m k : ℕ}
    (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ)
    (hclosed : ∀ i : Fin k, ∃ j : Fin k, P j = MvPolynomial.pderiv (Fin.last m) (P i))
    (x₀ : Fin m → ℝ) {t₀ : ℝ}
    (hex : ∃ i : Fin k, (Work.WilE4.spec (P i) x₀).eval t₀ = 0 ∧ Work.WilE4.spec (P i) x₀ ≠ 0) :
    ∃ i₀ : Fin k, (Work.WilE4.spec (P i₀) x₀).eval t₀ = 0 ∧ Work.WilE4.spec (P i₀) x₀ ≠ 0 ∧
      (Work.WilE4.spec (P i₀) x₀).rootMultiplicity t₀ = 1 ∧
      ∀ i : Fin k, (Work.WilE4.spec (P i) x₀).eval t₀ = 0 → Work.WilE4.spec (P i) x₀ ≠ 0 →
        (Work.WilE4.spec (P i₀) x₀).rootMultiplicity t₀
          ≤ (Work.WilE4.spec (P i) x₀).rootMultiplicity t₀ := by
  classical
  -- `q n` says that some member of the family specialises to a non-zero polynomial vanishing at
  -- `t₀` with root multiplicity exactly `n`.
  set q : ℕ → Prop := fun n => ∃ i : Fin k,
      (Work.WilE4.spec (P i) x₀).eval t₀ = 0 ∧ Work.WilE4.spec (P i) x₀ ≠ 0 ∧
      (Work.WilE4.spec (P i) x₀).rootMultiplicity t₀ = n
  have hqne : ∃ n, q n := by
    obtain ⟨i, hi0, hine⟩ := hex
    exact ⟨_, i, hi0, hine, rfl⟩
  obtain ⟨i₀, hi₀0, hi₀ne, hi₀mult⟩ := Nat.find_spec hqne
  -- A non-zero polynomial vanishing at `t₀` has root multiplicity at least one.
  have hi₀root : (Work.WilE4.spec (P i₀) x₀).IsRoot t₀ := hi₀0
  have hge1 : 1 ≤ (Work.WilE4.spec (P i₀) x₀).rootMultiplicity t₀ :=
    Nat.succ_le_of_lt ((Polynomial.rootMultiplicity_pos' (p := Work.WilE4.spec (P i₀) x₀)
      (x := t₀)).2 ⟨hi₀ne, hi₀root⟩)
  -- The minimal multiplicity is one: otherwise differentiating gives a strictly smaller one.
  have hle1 : (Work.WilE4.spec (P i₀) x₀).rootMultiplicity t₀ ≤ 1 := by
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨j, hj⟩ := hclosed i₀
    set p := Work.WilE4.spec (P i₀) x₀ with hpdef
    have hspecj : Work.WilE4.spec (P j) x₀ = p.derivative := by
      rw [hj, Work.WilE4.Poly.spec_pderiv, hpdef]
    have hroot : p.IsRoot t₀ := hi₀0
    have hmul : p.rootMultiplicity t₀ = Nat.find hqne := hi₀mult
    have hpos : 0 < p.rootMultiplicity t₀ := by rw [hmul]; omega
    have hnzd : ((p.rootMultiplicity t₀ : ℕ) : ℝ) ∈ nonZeroDivisors ℝ := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact_mod_cast (ne_of_gt hpos)
    have hdm : (p.derivative).rootMultiplicity t₀ = p.rootMultiplicity t₀ - 1 :=
      Polynomial.derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hroot hnzd
    have hdm_ne : p.derivative ≠ 0 := by
      intro hzero
      rw [hzero, Polynomial.rootMultiplicity_zero] at hdm
      omega
    have hdroot : (p.derivative).IsRoot t₀ := by
      have : 0 < (p.derivative).rootMultiplicity t₀ := by rw [hdm]; omega
      exact ((Polynomial.rootMultiplicity_pos' (p := p.derivative) (x := t₀)).1 this).2
    have hqn : q (p.rootMultiplicity t₀ - 1) := by
      refine ⟨j, ?_, ?_, ?_⟩
      · rw [hspecj]; exact hdroot
      · rw [hspecj]; exact hdm_ne
      · rw [hspecj]; exact hdm
    have hmin := Nat.find_min' hqne hqn
    omega
  have hmul1 : (Work.WilE4.spec (P i₀) x₀).rootMultiplicity t₀ = 1 := le_antisymm hle1 hge1
  have hfind_eq : Nat.find hqne = 1 := by rw [← hi₀mult, hmul1]
  refine ⟨i₀, hi₀0, hi₀ne, hmul1, ?_⟩
  -- Minimality of the chosen multiplicity.
  intro i hi0 hine
  have : q ((Work.WilE4.spec (P i) x₀).rootMultiplicity t₀) := ⟨i, hi0, hine, rfl⟩
  have hmin := Nat.find_min' hqne this
  rw [hmul1]
  omega

end Work.WilE4.CAD
