import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.EnvFacts
import Submission.Work.BoseBoxFock.exists_excLift
import Submission.Work.BoseBoxFock.hN_honest
import Submission.Work.BoseBoxFock.nPlusC_toCFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.NWindow_lift_honest` — the window condition `1_{[0,𝓜]}(n₊)` lifts to the lattice

FS's spectral window `eq:LocalizedAftercNumber` is the condition
`Φ = 1_{[0,𝓜]}(n₊)Φ` on a state of the *excited* (spectator) Fock space
`cfock (Excited m)`, recorded algebraically by `Work.BoseB7A.TildeData.NWindow`
as a finite decomposition `Φ = Σ_{m ≤ ⌊𝓜⌋₊} φ_m` into `n₊ = nPlusC`-eigenvectors
with eigenvalues `m`.

The bridge to the mode lattice (`Work.BoseB4.RealFock m ↔ FockCore (cfock (Excited m))`
via `Work.BoseB4.split`) evaluates FS's estimates on a *lattice* state `f` whose
condensate-free slice is `x = Φ`.  For the estimates the window condition must be
available in the lattice picture as well, i.e. `T.NWindow M f` for the lattice number
operator `T.N` (= `totNumOp m` for the honest family, `hN_honest`): the whole point is
that `1_{[0,𝓜]}(n₊)` is *exactly* `1_{[0,𝓜]}(T.N)` on the condensate-free slice.

## Proof

`Work.BoseB4.split` intertwines `totNumOp m` with `numOp + lift nPlusC`
(`hN_split_totNumOp`), so on the condensate-free slice (condensate level `0`, where
`numOp = 0`) it intertwines `totNumOp m` with `nPlusC`.

* `NWindowLift.coord_eq_zero_of_nPlusC_eigen`: the `β`-coordinate of an `n₊`-eigenvector
  of eigenvalue `j` vanishes unless `Finsupp.degree β = j`.  (In the `Finsupp` model
  `n₊` is the degree operator, `nPlusC_toCFock`.)
* Hence, since `x = Σ_{j ≤ ⌊𝓜⌋₊} φ_j` has *real* coordinates (`hre`), so does every
  `φ_j` with `j ∈ range (⌊𝓜⌋₊ + 1)`: for such a `j` and `β` either `degree β ≠ j` and
  the coordinate is `0`, or `degree β = j`, in which case `j` occurs in the sum and
  the coordinate of `φ_j` is the (`β`-real) coordinate of `x`.
* `Work.BoseBoxFock.exists_excLift` therefore produces lattice states `ψ_j` with
  `split ψ_j = single 0 (φ_j)`; `f := Σ_{j ∈ range (⌊𝓜⌋₊+1)} ψ_j` has
  `split f = single 0 x`, and `split` is injective (`NWindowLift.split_injective`,
  from the ℓ²-isometry `Split_inner` and positive definiteness of the Bombieri form),
  so `totNumOp m (ψ_j) = j • ψ_j` follows from the eigenvalue relation on the slice.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NWindowLift

/-! ## 1. Reading off a coordinate of a diagonal `Finsupp` operator -/

/-- The `β`-coordinate of `g.sum (fun b c => D b • single b c)`: only the term `b = β`
survives, and it multiplies the coefficient `g β` by `D β`. -/
lemma sum_smul_single_apply {X : Type*} [DecidableEq X] (D : (X →₀ ℕ) → ℂ)
    (g : (X →₀ ℕ) →₀ ℂ) (β : X →₀ ℕ) :
    (g.sum (fun b c => D b • Finsupp.single b c)) β = D β * g β := by
  rw [Finsupp.sum_apply, Finsupp.sum]
  rw [Finset.sum_eq_single β]
  · rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul]
  · intro b _ hne
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (Ne.symm hne), smul_zero]
  · intro hnot
    have h0 : g β = 0 := by
      by_contra hcon
      exact hnot (Finsupp.mem_support_iff.mpr hcon)
    rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, h0, mul_zero]

/-! ## 2. The coordinates of an `n₊`-eigenvector -/

/-- **Coordinates of an `n₊`-eigenvector.**  In the `Finsupp` model of the spectator space
the operator `nPlusC` is the total degree (`nPlusC_toCFock`), so an eigenvector with
eigenvalue `j` has vanishing coordinates in every multi-index of degree `≠ j`. -/
lemma coord_eq_zero_of_nPlusC_eigen {m : ℕ} [NeZero m] {v : cfock (Excited m)}
    {j : ℕ} (hv : nPlusC (m := m) v = (j : ℝ) • v) :
    ∀ β : Excited m →₀ ℕ, Finsupp.degree β ≠ j → ((toCFock (Excited m)).symm v) β = 0 := by
  intro β hβ
  set T := toCFock (Excited m) with hT
  set g : (Excited m →₀ ℕ) →₀ ℂ := T.symm v with hg
  have h1 : T.symm (nPlusC (m := m) v)
      = g.sum (fun b c => (((Finsupp.degree b : ℕ) : ℝ) : ℂ) • Finsupp.single b c) := by
    have hTg : T g = v := LinearEquiv.apply_symm_apply T v
    conv_lhs => rw [← hTg]
    rw [nPlusC_toCFock]
    exact LinearEquiv.symm_apply_apply T _
  have h2 : T.symm ((j : ℝ) • v) = ((j : ℝ) : ℂ) • g := by
    rw [show (j : ℝ) • v = ((j : ℝ) : ℂ) • v from rfl, map_smul]
  have h3 : g.sum (fun b c => (((Finsupp.degree b : ℕ) : ℝ) : ℂ) • Finsupp.single b c)
      = ((j : ℝ) : ℂ) • g := by
    rw [← h1, hv, h2]
  have h4 := congrArg (fun w : (Excited m →₀ ℕ) →₀ ℂ => w β) h3
  rw [sum_smul_single_apply, Finsupp.smul_apply, smul_eq_mul] at h4
  have hne : (((Finsupp.degree β : ℕ) : ℝ) : ℂ) ≠ ((j : ℝ) : ℂ) := by
    intro hcon
    have h2' : ((Finsupp.degree β : ℕ) : ℝ) = (j : ℝ) := by
      simpa using congrArg Complex.re hcon
    exact hβ (by exact_mod_cast h2')
  have h5 : ((((Finsupp.degree β : ℕ) : ℝ) : ℂ) - ((j : ℝ) : ℂ)) * g β = 0 := by
    rw [sub_mul, h4, sub_self]
  rcases mul_eq_zero.mp h5 with hz | hz
  · exact absurd (sub_eq_zero.mp hz) hne
  · exact hz

/-! ## 3. `split` is injective -/

/-- **The split is injective.**  `Work.BoseB4.split` is an isometry for the Bombieri form
(`Split_inner`), which is positive definite (`Bomb_self_eq_zero`). -/
lemma split_injective {m : ℕ} [NeZero m] : Function.Injective (split (m := m)) := by
  intro p q hpq
  have h0 : split (m := m) (p - q) = 0 := by rw [map_sub, hpq, sub_self]
  have hb : ((bomb m (p - q) (p - q) : ℝ) : ℂ) = 0 := by
    rw [← Split_inner, h0]
    simp [coreInner]
  have hb' : bomb m (p - q) (p - q) = 0 := by
    simpa using congrArg Complex.re hb
  exact sub_eq_zero.mp (Bomb_self_eq_zero hb')

/-! ## 4. The condensate annihilation on the condensate-free slice -/

/-- `numOp` kills the condensate level `0`: `numOp (single 0 v) = 0`. -/
lemma numOp_single_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : E) :
    numOp (Finsupp.single (0 : ℕ) v) = 0 := by
  show a0d (a0 (Finsupp.single (0 : ℕ) v)) = 0
  rw [a0_single]
  simp

/-- On the condensate-free slice the lattice number operator is `nPlusC`:
`(numOp + lift nPlusC) (single 0 v) = single 0 (nPlusC v)`. -/
lemma numOp_add_lift_nPlusC_single {m : ℕ} [NeZero m] (v : cfock (Excited m)) :
    (numOp (E := cfock (Excited m)) + lift (nPlusC (m := m)))
        (Finsupp.single (0 : ℕ) v)
      = Finsupp.single (0 : ℕ) (nPlusC (m := m) v) := by
  rw [LinearMap.add_apply, numOp_single_zero, lift_single, zero_add]

end NWindowLift

/-! ## 5. The lift -/

theorem NWindow_lift_honest (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ M : ℝ) (x : Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m))
    (hre : ∀ β : Work.BoseB4.Excited (HM μ).m →₀ ℕ,
      ((Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm x β).im = 0)
    (hdec : ∃ φ : ℕ → Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m),
      (∀ j : ℕ, Work.BoseBoxFock.nPlusC (m := (HM μ).m) (φ j) = (j : ℝ) • φ j)
        ∧ x = ∑ j ∈ Finset.range (⌊M⌋₊ + 1), φ j) :
    ∃ f : Work.BoseB4.RealFock (HM μ).m,
      Work.BoseB4.split f = Finsupp.single 0 x
        ∧ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow M f := by
  classical
  obtain ⟨φ, hφeig, hφsum⟩ := hdec
  -- ## The coordinates of `φ j`
  have hsupp : ∀ j ∈ Finset.range (⌊M⌋₊ + 1),
      ∀ β : Work.BoseB4.Excited (HM μ).m →₀ ℕ,
        Finsupp.degree β ≠ j →
          ((Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm (φ j)) β = 0 :=
    fun j _ β hβ => NWindowLift.coord_eq_zero_of_nPlusC_eigen (hφeig j) β hβ
  have hsumcoord : ∀ β : Work.BoseB4.Excited (HM μ).m →₀ ℕ,
      ((Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm x) β
        = ∑ j ∈ Finset.range (⌊M⌋₊ + 1),
            ((Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm (φ j)) β := by
    intro β
    have hsplit : (Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm x
        = ∑ j ∈ Finset.range (⌊M⌋₊ + 1),
            (Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm (φ j) := by
      rw [hφsum, map_sum]
    rw [hsplit, Finsupp.finsetSum_apply]
  -- ## Realness of the coordinates of `φ j`, `j ∈ range (⌊𝓜⌋₊+1)`
  have hreal : ∀ j ∈ Finset.range (⌊M⌋₊ + 1),
      ∀ β : Work.BoseB4.Excited (HM μ).m →₀ ℕ,
        (((Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm (φ j)) β).im = 0 := by
    intro j hj β
    by_cases hd : Finsupp.degree β = j
    · have hsingle : ∑ k ∈ Finset.range (⌊M⌋₊ + 1),
          ((Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm (φ k)) β
          = ((Work.BoseB4.toCFock (Work.BoseB4.Excited (HM μ).m)).symm (φ j)) β := by
        refine Finset.sum_eq_single j ?_ ?_
        · intro k hk hkj
          refine hsupp k hk β ?_
          rw [hd]
          exact fun h => hkj h.symm
        · intro hjnot
          exact absurd hj hjnot
      rw [← hsingle, ← hsumcoord β, hre β]
    · simpa using congrArg Complex.im (hsupp j hj β hd)
  -- ## The lifts `ψ j`
  have hex : ∀ j : ℕ, ∃ f : Work.BoseB4.RealFock (HM μ).m,
      (j ∈ Finset.range (⌊M⌋₊ + 1) → Work.BoseB4.split f = Finsupp.single 0 (φ j))
        ∧ (j ∉ Finset.range (⌊M⌋₊ + 1) → f = 0) := by
    intro j
    by_cases hj : j ∈ Finset.range (⌊M⌋₊ + 1)
    · obtain ⟨f, hf⟩ := Work.BoseBoxFock.exists_excLift (φ j) (hreal j hj)
      exact ⟨f, fun _ => hf, fun h => absurd hj h⟩
    · exact ⟨0, fun h => absurd h hj, fun _ => rfl⟩
  choose ψ hψ hψzero using hex
  -- ## `ψ j` is a `totNumOp`-eigenvector of eigenvalue `j`
  have hψeig : ∀ j : ℕ,
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.N (ψ j) = (j : ℝ) • ψ j := by
    intro j
    by_cases hj : j ∈ Finset.range (⌊M⌋₊ + 1)
    · apply NWindowLift.split_injective
      rw [hN_honest v h fc fu HM μ (ψ j), hN_op_identity, hψ j hj, map_smul, hψ j hj,
        NWindowLift.numOp_add_lift_nPlusC_single, hφeig j, ← Finsupp.smul_single]
    · change Work.BoseB4.totNumOp (HM μ).m (ψ j) = (j : ℝ) • ψ j
      rw [hψzero j hj, map_zero, smul_zero]
  -- ## Assembly
  have hsplitf : Work.BoseB4.split (∑ j ∈ Finset.range (⌊M⌋₊ + 1), ψ j)
      = Finsupp.single 0 x := by
    rw [map_sum]
    have hsum : ∑ j ∈ Finset.range (⌊M⌋₊ + 1), Work.BoseB4.split (ψ j)
        = ∑ j ∈ Finset.range (⌊M⌋₊ + 1), Finsupp.single 0 (φ j) :=
      Finset.sum_congr rfl (fun j hj => hψ j hj)
    rw [hsum, ← Finsupp.single_finsetSum, ← hφsum]
  refine ⟨∑ j ∈ Finset.range (⌊M⌋₊ + 1), ψ j, hsplitf, ?_⟩
  show ∃ φ : ℕ → Work.BoseB4.RealFock (HM μ).m,
      (∀ m : ℕ,
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.N (φ m) = (m : ℝ) • φ m)
        ∧ (∑ j ∈ Finset.range (⌊M⌋₊ + 1), ψ j)
            = ∑ m ∈ Finset.range (⌊M⌋₊ + 1), φ m
  exact ⟨ψ, hψeig, rfl⟩

end Work.BoseBoxFock
