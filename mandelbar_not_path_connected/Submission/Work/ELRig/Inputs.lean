/-
# ELRig — the inputs from the sibling areas ELTop, ELPull and ELNest

`NOTES_LEAD_mandelbar_EL_F_contracts.md` §6 specifies ELRig as the last of the four EL areas: it
*consumes* `ELTop` (the plane topology of the ray polygons), `ELPull` (the pull-back pairs, the
orbit portrait and the rational certificate) and `ELNest` (the two shrinking nests and the side
preservation `SP`).  Those three areas live in sibling directories and are being proved in
parallel; until they land, their outputs enter ELRig's theorems as the *explicit hypotheses*
packaged in the three structures below:

* `Z1Nest` : the nest at the parabolic point `z₁`, the side preservation, and the position of the
  attracting petal in the wake side of the `α`-pair (ELNest, items N1–N4 and R-a1 `SP`);
* `B2Data` : the tripod at the branch point `b₂`, the rotation of its arms by `F`, the nest at
  `b₂` and its cut points (ELNest N3–N4, ELPull P5/P6 certificate C7, ELTop T8);
* `LiftSides` : the plane topology of the two `1`-periodic lift curves of the ray tails in the
  repelling coordinate (R-a2's "periodic-curve two-sides lemma", ELTop's plane topology).

Each field is a mathematical statement that the corresponding sibling area delivers; none of them
mentions the conclusion `∃ x, Ψ x ∉ K c` or anything equivalent to it.
-/
import Submission.Work.ELRig.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.EL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The nest at `z₁` -/

/-- **The nest at the parabolic point `z₁`** (ELNest items N1–N4 and the side preservation `SP`
of R-a1, in the vocabulary of `Work.EL`).

* `P0` is the `α`-pair at `z₁` and `Q n` is the level-`n` pair of the nest;
* `shrinks` is N2 (`Qnest_shrinks`): the region between the two pairs on the near sides contains
  no point of `K` at distance `> ε` from `z₁`;
* `z1_near_Q` says that `z₁` lies on the near side of every `Q n`: the nest hugs the near side of
  the `α`-pair at the parabolic point;
* `shift`/`base_shift` are N1: `F` maps the level-`n+1` landing point to the level-`n` one, and
  the level-`0` pair is a pull-back of the pair of `f^4 z₁`;
* `SP` is the side preservation of R-a1;
* `Pa_far` is the portrait statement (ELPull's L-wake at `k ≡ 1` together with `SP`) that the
  attracting petal of the flower lies in the wake side of the `α`-pair. -/
structure Z1Nest {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (z₁ : ℂ) (Pa : Set ℂ) where
  /-- the `α`-pair. -/
  P0 : CoPair hN
  /-- the angles and landing point of `P0`. -/
  P0_spec : P0.a = alpha1 ∧ P0.b = alpha2 ∧ P0.y = z₁
  /-- the two-sidedness of the `α`-pair. -/
  sides_P0 : PairSides hN P0
  /-- the level-`n` pair of the nest. -/
  Q : ℕ → CoPair hN
  /-- the two-sidedness of each level-`n` pair. -/
  sides_Q : ∀ n : ℕ, PairSides hN (Q n)
  /-- **N2**: the nest regions shrink to `z₁`. -/
  shrinks : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ K c,
    z ∈ pairSideNear (Q n) → z ∈ pairSideNear P0 → ‖z - z₁‖ < ε
  /-- `z₁` lies on the near side of every level-`n` pair. -/
  z1_near_Q : ∀ n : ℕ, z₁ ∈ pairSideNear (Q n)
  /-- the level-`n` pair does not land at `z₁` (the orbit portrait of the root). -/
  Q_ne_z1 : ∀ n : ℕ, (Q n).y ≠ z₁
  /-- **N1**: the level-`n+1` landing point maps to the level-`n` one. -/
  shift : ∀ n : ℕ, F c ((Q (n + 1)).y) = (Q n).y
  /-- **N1/P6**: the level-`0` pair is a pull-back of the pair landing at `f^4 z₁`. -/
  base_shift : F c ((Q 0).y) = (Tantibar c)^[4] z₁
  /-- **R-a1, `SP`**: the side of the `α`-pair is preserved by `F` near `z₁`. -/
  SP : ∃ ρ > 0, ∀ z ∈ Metric.ball z₁ ρ, z ∉ pairCurve P0 →
    (z ∈ pairSide P0 ↔ F c z ∈ pairSide P0)
  /-- **the portrait**: the attracting petal lies in the wake side of the `α`-pair. -/
  Pa_far : Pa ⊆ pairSide P0

/-! ## The tripod at `b₂` -/

/-- The three arms of the tripod, as an index type. -/
inductive ArmIdx : Type
  /-- the arm bounded by the rays `22/63` and `25/63`. -/
  | A : ArmIdx
  /-- the arm bounded by the rays `25/63` and `37/63`. -/
  | B : ArmIdx
  /-- the arm bounded by the rays `37/63` and `85/63`. -/
  | C : ArmIdx
deriving DecidableEq, Inhabited

/-- The rotation of the arms induced by `F = (T_c)^{10}`, from the certificate `C7`:
`A ↦ C ↦ B ↦ A`. -/
def ArmIdx.rot : ArmIdx → ArmIdx
  | A => C
  | B => A
  | C => B

theorem ArmIdx.rot_ne_self (Z : ArmIdx) : ArmIdx.rot Z ≠ Z := by
  cases Z <;> simp [ArmIdx.rot]

theorem ArmIdx.rot_cycle (Z : ArmIdx) : ArmIdx.rot (ArmIdx.rot (ArmIdx.rot Z)) = Z := by
  cases Z <;> simp [ArmIdx.rot]

/-- The arms of a tripod, as a function of the index type. -/
def armOf {c : ℂ} {φ : ℂ → ℂ} {hN : DynB c φ} {y : ℂ} (T : TripodSides hN y) :
    ArmIdx → Set ℂ
  | ArmIdx.A => armA hN y T.lands_a T.lands_b
  | ArmIdx.B => armB hN y T.lands_b T.lands_c
  | ArmIdx.C => armC hN y T.lands_c T.lands_a'

/-- **The tripod data at the branch point `b₂`** (ELNest N3–N4, ELPull certificate `C7`, ELTop
T8).

* `tripod` : the three arms are the three components of the complement of the tripod curve;
* `rot` : the certificate `C7`: `F` maps the arm `Z` onto the arm `rot Z`;
* `z1_mem_A`, `z0_notMem_clA` : the two points `z₁` and `z₀ = f^4 z₁` lie in different arms
  (the certificate of §2: `z₁ ∈ X_A`, `z₀ ∉ closure X_A`);
* `Δ`, `cutA/B/C` : the nest at `b₂` and its cut points: `Δ n` is a neighbourhood of `b₂`
  shrinking to `b₂`, and in each arm the only point of `K ∩ frontier (Δ n)` is the cut point. -/
structure B2Data {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (z₁ : ℂ) where
  /-- the branch point. -/
  b₂ : ℂ
  /-- `b₂` is fixed by the holomorphic second return map `Tsq c = (T_c)^2`. -/
  b2_fix : Work.Landing.Tsq c b₂ = b₂
  /-- **`b₂` is not postcritical**: no point of the forward orbit of the critical point `0` is
  `b₂`.  (The critical orbit converges to the parabolic point `z₁ ≠ b₂`, and `b₂` is periodic
  under `Tsq c`.)  This is what makes `b₂` a non-critical value of every iterate of `Tsq c`
  (`Work.ELRig.deriv_iterate_ne_zero_of_notMem_orbit`), hence `Ψ` locally biholomorphic at the
  preimages of `b₂`. -/
  b2_not_postcrit : ∀ n : ℕ, (Tantibar c)^[n] 0 ≠ b₂
  /-- the tripod at `b₂`. -/
  tripod : TripodSides hN b₂
  /-- the parabolic point `z₁` lies in the arm `A`. -/
  z1_mem_A : z₁ ∈ armOf tripod ArmIdx.A
  /-- the point `z₀ = f^4 z₁`, the landing point of the level-`0` pair of the `z₁`-nest, lies
  outside the closure of the arm `A`. -/
  z0_notMem_clA : (Tantibar c)^[4] z₁ ∉ closure (armOf tripod ArmIdx.A)
  /-- the nest regions at `b₂`. -/
  Δ : ℕ → Set ℂ
  /-- each level is a neighbourhood of `b₂`. -/
  isOpen_Δ : ∀ n : ℕ, IsOpen (Δ n)
  /-- `b₂` lies in every level. -/
  b2_mem_Δ : ∀ n : ℕ, b₂ ∈ Δ n
  /-- the nest shrinks to `b₂`. -/
  Δ_shrinks : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, Δ n ⊆ Metric.ball b₂ ε
  /-- the cut point of the arm `Z` at level `n`. -/
  cut : ArmIdx → ℕ → ℂ
  /-- the cut point lies in the arm, in `K` and on the frontier of the nest. -/
  cut_mem : ∀ (Z : ArmIdx) (n : ℕ), cut Z n ∈ armOf tripod Z ∩ K c ∩ frontier (Δ n)
  /-- there is no other point of `K` on the frontier of the nest in that arm. -/
  cut_unique : ∀ (Z : ArmIdx) (n : ℕ), frontier (Δ n) ∩ K c ∩ armOf tripod Z = {cut Z n}
  /-- the certificate `C7` in the **point form** used by the rigidity argument (`ELNest`'s N5):
  for all large `n`, `F` moves the level-`n` cut point of the arm `Z` into the arm `rot Z`.
  (A *global* statement `F '' armZ = arm (rot Z)` is false: `F` is a degree-`1024` polynomial
  fixing `b₂`, so it would force `z₁ ∈ armA ∩ armC`.) -/
  rot_cut : ∃ N : ℕ, ∀ (Z : ArmIdx) (n : ℕ), N ≤ n →
    F c (cut Z n) ∈ armOf tripod (ArmIdx.rot Z)


/-! ## The plane topology of the two lift curves -/

/-- **The `1`-periodic lift curves of the ray tails and their two-sidedness** (R-a2's
"periodic-curve two-sides lemma": the plane topology of two periodic curves in the repelling
coordinate, ELTop's business).

* `γ₁`, `γ₂` are the `1`-periodic lifts of the two ray tails, with `γ₂ = ι γ₁` for
  `ι w = conj w + 1/2`;
* `U`, `M`, `L` are the three regions cut out by them in the left half plane `Re < -R`, with `U`
  above both, `L` below both and `M` the middle region containing the real axis;
* `decomp` : every preconnected subset of the left half plane off the two curves lies in one of
  `U`, `M`, `L`;
* `top_mem_U`/`bottom_mem_L` : `U` and `L` reach the strips `|Im| > R₀`. -/
structure LiftSides {c : ℂ} {φ : ℂ → ℂ} (hN : DynB c φ) (z₁ : ℂ) (γ₁ γ₂ : ℝ → ℂ)
    (R R₀ : ℝ) where
  /-- the half-plane level is above the strip level of the flower's `Ψ_ends`. -/
  hRR₀ : R₀ < R
  /-- the upper region. -/
  U : Set ℂ
  /-- the middle region, containing the real axis. -/
  M : Set ℂ
  /-- the lower region. -/
  L : Set ℂ
  /-- the three regions are contained in the left half plane. -/
  U_sub : U ⊆ {w : ℂ | w.re < -R}
  M_sub : M ⊆ {w : ℂ | w.re < -R}
  L_sub : L ⊆ {w : ℂ | w.re < -R}
  /-- they avoid the two lift curves. -/
  U_off : U ∩ (Set.range γ₁ ∪ Set.range γ₂) = ∅
  M_off : M ∩ (Set.range γ₁ ∪ Set.range γ₂) = ∅
  L_off : L ∩ (Set.range γ₁ ∪ Set.range γ₂) = ∅
  /-- the three regions are preconnected. -/
  U_conn : IsPreconnected U
  M_conn : IsPreconnected M
  L_conn : IsPreconnected L
  /-- they are pairwise disjoint. -/
  U_disj_M : Disjoint U M
  U_disj_L : Disjoint U L
  M_disj_L : Disjoint M L
  /-- together with the two lift curves they cover the left half plane. -/
  cover : {w : ℂ | w.re < -R} ⊆ U ∪ M ∪ L ∪ Set.range γ₁ ∪ Set.range γ₂
  /-- the real axis below the level `-R` lies in the middle region. -/
  real_mem_M : ∀ x : ℝ, x < -R → (x : ℂ) ∈ M
  /-- the middle region is the region containing the real axis: every preconnected subset of
  the left half plane avoiding the two lifts lies in one of the three regions. -/
  decomp : ∀ S : Set ℂ, IsPreconnected S → S ⊆ {w : ℂ | w.re < -R} →
    S ∩ (Set.range γ₁ ∪ Set.range γ₂) = ∅ → S ⊆ U ∨ S ⊆ M ∨ S ⊆ L
  /-- the upper region reaches the strip `Im > R₀`. -/
  top_mem_U : ∃ w ∈ U, R₀ < w.im
  /-- the lower region reaches the strip `Im < -R₀`. -/
  bottom_mem_L : ∃ w ∈ L, w.im < -R₀

end Work.EL
