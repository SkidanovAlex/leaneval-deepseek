/-
  WilC4 : **H3** of the C4 route (`sources/wilkiesC4route/wilkies_C4_route.md` §3):
  ULPM in `M` gives the *Gap lemma*.

  `ModelULPM M` is the uniform log-piecewise-monomiality of `M`-definable families: for every
  `∅`-definable functional family `Y ⊆ M^{k+2}` (`x ↦ y`, parameters `c : Fin k → M`) there are
  `N > 0`, a finite exponent set `Qs` and an `∅`-definable breakpoint set `B ⊆ M^{k+1}` with
  `|B_c| ≤ N`, such that positive `x₁, x₂` on the same side of every breakpoint `b ∈ B_c` at
  distance factor `N` have the same domain status and
  `|y₂| x₁^q ≍_N |y₁| x₂^q` for some `q ∈ Qs`.

  `GapLemma M` says: for a `dcl`-closed `T`, `a > 0` not comparable with any nonzero element of
  `T`, and `z ∈ Dcl T {a}`, `z ≠ 0`, there are `p : ℤ`, `n > 0` and `α ∈ T`, `α ≠ 0` with
  `z^n / (α a^p)` a unit.

  ## Proof

  Write `z = F(c, a)` with `c ∈ T` (`exists_Tdefinable_fibre` gives a `T`-definable graph `Z`
  with `(z, a) ∈ Z` and singleton fibre at `a`; `exists_ulpm_family` bundles the `T`-parameters
  of `Z` into the finitely many coordinates `c` of a *parameter-free* family `Y`, functional in
  every parameter, whose `c`-fibre is the functionalised version of `Z`).

  Apply `ModelULPM M` to `Y`: get `N`, `Qs` and the breakpoint set `B`.  For the parameter value
  `c` the fibre `D = B_c` is finite (`|D| ≤ N`), `T`-definable, hence `D ⊆ T`
  (`finiteDefinable_subset_T`); also `a ∉ D` (else `a ∈ T` and `ValEq a a` contradicts the gap
  hypothesis).

  *Gap lemma for breakpoints.*  If `b ∈ T`, `b ≠ 0` and `b < a`, then `¬ ValEq a b` says that
  `b` is *infinitesimal* with respect to `a`: `n b < a` for every `n ≥ 1`.  Symmetrically
  `a < b` makes `b` infinite with respect to `a`: `n a < b` for every `n ≥ 1`.

  *Choice of `x₁`.*  Put `bm = max(D ∩ (0,a))` when this is nonempty and `x₁ = 2N bm`; then
  `x₁ ∈ T`, `0 < x₁`, and `x₁` is on the same side of every `b ∈ D` as `a` at factor `N`
  (for `b ∈ D` with `b > a` use `N x₁ = 2N² bm < a < b`, which is the strong form of the gap
  consequence for `bm`).  If `D ∩ (0,a) = ∅` but `D ∩ (a,∞) ≠ ∅` take `bp = min(D ∩ (a,∞))` and
  `x₁ = bp/(2N)`; if `D = ∅` take `x₁ = 1`.

  *Conclusion.*  `SameSide N D x₁ a`, so the domain clause of ULPM gives `y₁` with
  `Fin.cons x₁ (Fin.cons y₁ c) ∈ Y`; `y₁` is the unique such element, so `y₁ ∈ T`.  The ratio
  clause gives `q = p/n ∈ Qs`, `t₁, t₂` with `IsRpow x₁ q t₁`, `IsRpow a q t₂` and
  `|z| t₁ ≤ N |y₁| t₂`, `|y₁| t₂ ≤ N |z| t₁`.  Then `y₁ ≠ 0` (else `z = 0`), `t₁^n = x₁^p`,
  `t₂^n = a^p`, and `α = y₁^n / x₁^p ∈ T` satisfies
  `z^n / (α a^p) = (z t₁/(y₁ t₂))^n`, a power of a unit.  ∎

  All auxiliary inputs are named lemmas of `Submission.Work.WilC4g` (or of this area's vocabulary
  files): `exists_Tdefinable_fibre`, `exists_ulpm_family`, `finiteDefinable_subset_T`,
  `definable_fibre_cons`, `definable_prepend`, `isRpow_canon`, `unitVal_zpow`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilC4.exists_Tdefinable_fibre
import Submission.Work.WilC4.sup_exists_dcl
import Submission.Work.WilC4.isRpow_canon
import Submission.Work.WilC4.unitVal_zpow
import Submission.Work.WilC4.valEq_refl
import Submission.Work.WilC4.dcl_add
import Submission.Work.WilC4.dcl_mul
import Submission.Work.WilC4.dcl_inv
import Submission.Work.WilC4.dcl_neg
import Submission.Work.WilC4.definableElt_of_mem_left
import Submission.Work.WilC2.Square
import Submission.Work.WilC4g.definable_fibre_cons
import Submission.Work.WilC4g.definable_prepend
import Submission.Work.WilC4g.exists_ulpm_family
import Submission.Work.WilC4g.finiteDefinable_subset_T

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
open Classical
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG FirstOrder FirstOrder.Language
open Work.WilC2 (ringToLRc liftR liftR_realize leF leF_realize_le)

section Helpers

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [FirstOrder.Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]

/-! ## 0. `T` is closed under the field operations and contains the constants -/

/-- `(1 : M) ∈ T` for a `dcl`-closed `T`: the singleton `{1}` is cut out by the
parameter-free formula `x = 1`. -/
lemma one_mem_T {T : Set M} (hTdcl : ∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) :
    (1 : M) ∈ T := by
  have hdef : (∅ : Set M).Definable LRc {fun _ : Fin 1 => (1 : M)} := by
    rw [Set.empty_definable_iff]
    refine ⟨liftR (fun i : Fin 1 => i)
      (Term.equal (Term.var (0 : Fin 1))
        (1 : Language.ring.Term (Fin 1))), ?_⟩
    ext u
    rw [Set.mem_ofPred_eq, liftR_realize]
    simp only [Set.mem_singleton_iff, Formula.realize_equal, Term.realize_var,
      Ring.realize_one, Function.comp_apply]
    constructor
    · intro h
      exact congrFun h 0
    · intro h
      funext i
      fin_cases i
      exact h
  refine (hTdcl 1).mp ?_
  rw [DefinableElt, Set.union_empty]
  exact hdef.mono (Set.empty_subset T)

/-- `T` is closed under addition. -/
lemma add_mem_T {T : Set M} (hTdcl : ∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) {x y : M}
    (hx : x ∈ T) (hy : y ∈ T) : x + y ∈ T :=
  (hTdcl _).mp (dcl_add ((hTdcl x).mpr hx) ((hTdcl y).mpr hy))

/-- `T` is closed under multiplication. -/
lemma mul_mem_T {T : Set M} (hTdcl : ∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) {x y : M}
    (hx : x ∈ T) (hy : y ∈ T) : x * y ∈ T :=
  (hTdcl _).mp (dcl_mul ((hTdcl x).mpr hx) ((hTdcl y).mpr hy))

/-- `T` is closed under negation. -/
lemma neg_mem_T {T : Set M} (hTdcl : ∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) {x : M}
    (hx : x ∈ T) : -x ∈ T :=
  (hTdcl _).mp (dcl_neg ((hTdcl x).mpr hx))

/-- `T` is closed under inversion of nonzero elements. -/
lemma inv_mem_T {T : Set M} (hTdcl : ∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) {x : M}
    (hx : x ∈ T) (hx0 : x ≠ 0) : x⁻¹ ∈ T :=
  (hTdcl _).mp (dcl_inv ((hTdcl x).mpr hx) hx0)

/-- `T` is closed under division by nonzero elements. -/
lemma div_mem_T {T : Set M} (hTdcl : ∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) {x y : M}
    (hx : x ∈ T) (hy : y ∈ T) (hy0 : y ≠ 0) : x / y ∈ T := by
  rw [div_eq_mul_inv]
  exact mul_mem_T hTdcl hx (inv_mem_T hTdcl hy hy0)

/-- `T` is closed under natural powers. -/
lemma pow_mem_T {T : Set M} (hTdcl : ∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) {x : M}
    (hx : x ∈ T) (k : ℕ) : x ^ k ∈ T := by
  induction k with
  | zero => simpa using one_mem_T hTdcl (T := T)
  | succ k ih => rw [pow_succ]; exact mul_mem_T hTdcl ih hx

/-- `T` is closed under integer powers of nonzero elements. -/
lemma zpow_mem_T {T : Set M} (hTdcl : ∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) {x : M}
    (hx : x ∈ T) (hx0 : x ≠ 0) (k : ℤ) : x ^ k ∈ T := by
  rcases k with k | k
  · simpa using pow_mem_T hTdcl hx k
  · rw [zpow_negSucc]
    exact inv_mem_T hTdcl (pow_mem_T hTdcl hx _) (pow_ne_zero _ hx0)

/-- `(k : M) ∈ T` for every `k : ℕ`. -/
lemma natCast_mem_T {T : Set M} (hTdcl : ∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) (k : ℕ) :
    (k : M) ∈ T := by
  induction k with
  | zero =>
    have h1 : (1 : M) ∈ T := one_mem_T hTdcl
    have h3 : (1 : M) + -(1 : M) ∈ T :=
      add_mem_T hTdcl h1 (neg_mem_T hTdcl h1)
    simpa using h3
  | succ k ih =>
    have h : (k : M) + 1 ∈ T := add_mem_T hTdcl ih (one_mem_T hTdcl)
    simpa [Nat.cast_succ] using h

/-! ## 1. Consequences of the gap hypothesis -/

/-- If `a > 0` is not comparable with `0 < b ∈ T` and `b < a`, then `b` is *infinitesimal*
with respect to `a`: every natural multiple of `b` is still smaller than `a`. -/
lemma gap_nmul_lt {T : Set M} {a b : M} (hgap : ∀ c ∈ T, c ≠ 0 → ¬ ValEq a c)
    (hbT : b ∈ T) (hb0 : b ≠ 0) (hb : 0 < b) (hba : b < a) (n : ℕ) (hn : 0 < n) :
    (n : M) * b < a := by
  have ha : 0 < a := lt_trans hb hba
  have hnpos : (0 : M) < (n : M) := by exact_mod_cast hn
  have hn1 : (1 : M) ≤ (n : M) := by exact_mod_cast hn
  have hinv : (n : M)⁻¹ ≤ 1 := by
    have h : (n : M)⁻¹ * 1 ≤ (n : M)⁻¹ * (n : M) :=
      mul_le_mul_of_nonneg_left hn1 (by positivity)
    rwa [mul_one, inv_mul_cancel₀ (ne_of_gt hnpos)] at h
  by_contra hcon
  rw [not_lt] at hcon
  refine hgap b hbT hb0 ⟨n, hn, ?_, ?_⟩
  · rw [abs_of_pos hb, abs_of_pos ha]
    calc (n : M)⁻¹ * b ≤ 1 * b := mul_le_mul_of_nonneg_right hinv hb.le
      _ = b := one_mul b
      _ ≤ a := hba.le
  · rw [abs_of_pos ha, abs_of_pos hb]; exact hcon

/-- If `a > 0` is not comparable with `0 < a < b ∈ T`, then `b` is *infinite* with respect to
`a`: `a` is smaller than every natural multiple of `b`. -/
lemma gap_nmul_gt {T : Set M} {a b : M} (hgap : ∀ c ∈ T, c ≠ 0 → ¬ ValEq a c)
    (hbT : b ∈ T) (hb0 : b ≠ 0) (ha : 0 < a) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    (n : M) * a < b := by
  have hbpos : 0 < b := lt_trans ha hab
  have hnpos : (0 : M) < (n : M) := by exact_mod_cast hn
  have hnne : (n : M) ≠ 0 := ne_of_gt hnpos
  by_contra hcon
  rw [not_lt] at hcon
  refine hgap b hbT hb0 ⟨n, hn, ?_, ?_⟩
  · rw [abs_of_pos hbpos, abs_of_pos ha]
    calc (n : M)⁻¹ * b ≤ (n : M)⁻¹ * ((n : M) * a) :=
          mul_le_mul_of_nonneg_left hcon (by positivity)
      _ = a := by rw [← mul_assoc, inv_mul_cancel₀ hnne, one_mul]
  · rw [abs_of_pos ha, abs_of_pos hbpos]
    have hn1 : (1 : M) ≤ (n : M) := by exact_mod_cast hn
    calc a ≤ b := hab.le
      _ ≤ (n : M) * b := le_mul_of_one_le_left hbpos.le hn1

/-! ## 2. The criterion for `SameSide`, and definable singletons -/

/-- **A sufficient criterion for `SameSide`.**  If `x₁, a > 0`, `a ∉ D`, and
* `N b < x₁` for every `b ∈ D` with `b ≤ 0`,
* `N b < x₁` and `N b < a` for every `b ∈ D` with `0 < b < a`,
* `N x₁ < b` and `N a < b` for every `b ∈ D` with `a < b`,
then `x₁` and `a` are on the same side of every element of `D`, beyond factor `N`. -/
lemma sameSide_of_aux {D : Set M} {N : ℕ} {a x₁ : M} (hx₁ : 0 < x₁) (ha : 0 < a)
    (haD : a ∉ D)
    (h₁ : ∀ b ∈ D, b ≤ 0 → (N : M) * b < x₁)
    (h₂ : ∀ b ∈ D, 0 < b → b < a → (N : M) * b < x₁ ∧ (N : M) * b < a)
    (h₃ : ∀ b ∈ D, a < b → (N : M) * x₁ < b ∧ (N : M) * a < b) :
    Route.SameSide N D x₁ a := by
  intro b hb
  rcases lt_trichotomy b a with hba | hba | hba
  · by_cases hb0 : b ≤ 0
    · have hle : (N : M) * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hb0
      exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inl (h₂ b hb (not_le.mp hb0) hba)
  · exact absurd (hba ▸ hb) haD
  · exact Or.inr (h₃ b hb hba)

/-- A `T`-definable singleton consists of a `T`-definable element. -/
lemma definableElt_of_singleton {T S : Set M} {x : M}
    (hS : T.Definable₁ LRc S) (h : S = {x}) : DefinableElt T ∅ x := by
  rw [DefinableElt, Set.union_empty]
  have hset : ({fun _ : Fin 1 => x} : Set (Fin 1 → M)) = {v : Fin 1 → M | v 0 ∈ S} := by
    rw [h]
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hv; rw [hv]
    · intro hv
      funext i
      rw [Subsingleton.elim i 0]
      exact hv
  rw [hset]
  exact hS

end Helpers

theorem gapLemma_of_ULPM {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] (hM : M ⊨ WilkiesDesign.CG.TR) (hU : Work.WilC4.Route.ModelULPM M) : Work.WilC4.Route.GapLemma M := by
  intro T hTdcl a ha hgap z hz hzne
  -- 1. the `T`-definable graph `Z` of `z` as a function of `a`
  obtain ⟨Z, hZd, hza, hZfib⟩ := exists_Tdefinable_fibre hz
  -- 2. bundle the `T`-parameters into finitely many coordinates: a parameter-free family `Y`
  obtain ⟨k, c, Y, hcT, hYdef, hYfun, hYfib⟩ := Work.WilC4g.exists_ulpm_family hZd
  -- 3. apply ULPM
  obtain ⟨N, hN, Qs, B, hBdef, hBc⟩ := hU k Y hYdef hYfun
  obtain ⟨hDcard, hD'⟩ := hBc c
  have hNpos : (0 : M) < (N : M) := by exact_mod_cast hN
  -- 4. the breakpoint fibre `D = B_c` is `T`-definable and finite, so `D ⊆ T`
  have hDdefT : T.Definable₁ LRc {x : M | Fin.cons x c ∈ B} := by
    have h := Work.WilC4g.definable_fibre_cons (A := (∅ : Set M)) hBdef c
    refine h.mono ?_
    rintro x (hx | ⟨i, rfl⟩)
    · exact absurd hx (Set.notMem_empty x)
    · exact hcT i
  have hDfin : {x : M | Fin.cons x c ∈ B}.Finite := Set.finite_of_encard_le_coe hDcard
  have hDsubT : ∀ x ∈ {x : M | Fin.cons x c ∈ B}, x ∈ T :=
    Work.WilC4g.finiteDefinable_subset_T hM hTdcl hDdefT hDfin
  have haD : a ∉ {x : M | Fin.cons x c ∈ B} := fun ha' =>
    hgap a (hDsubT a ha') (ne_of_gt ha) (valEq_refl a)
  -- 5. choose a positive `T`-point `x₁` on the same side of every breakpoint as `a`
  have hx₁ex : ∃ x₁ : M, x₁ ∈ T ∧ 0 < x₁ ∧
      Route.SameSide N {x : M | Fin.cons x c ∈ B} x₁ a := by
    set A₁ : Set M := {x : M | Fin.cons x c ∈ B ∧ 0 < x ∧ x < a} with hA₁def
    set A₂ : Set M := {x : M | Fin.cons x c ∈ B ∧ a < x} with hA₂def
    have hA₁fin : A₁.Finite := hDfin.subset (by intro x hx; rw [hA₁def] at hx; exact hx.1)
    have hA₂fin : A₂.Finite := hDfin.subset (by intro x hx; rw [hA₂def] at hx; exact hx.1)
    by_cases hne₁ : A₁.Nonempty
    · -- `bm = max(D ∩ (0,a))` exists
      obtain ⟨bm, hbmA₁, hbmmax⟩ := Set.exists_max_image A₁ id hA₁fin hne₁
      rw [hA₁def] at hbmA₁
      obtain ⟨hbmB, hbmpos, hbmlt⟩ := hbmA₁
      have hbmT : bm ∈ T := hDsubT bm hbmB
      have hbmne : bm ≠ 0 := ne_of_gt hbmpos
      set x₁ : M := ((2 * N : ℕ) : M) * bm with hx₁def
      have h2Npos : (0 : M) < ((2 * N : ℕ) : M) := by
        exact_mod_cast Nat.mul_pos (by norm_num) hN
      have hx₁T : x₁ ∈ T :=
        mul_mem_T hTdcl (natCast_mem_T hTdcl (2 * N)) hbmT
      have hx₁pos : 0 < x₁ := by rw [hx₁def]; exact mul_pos h2Npos hbmpos
      refine ⟨x₁, hx₁T, hx₁pos, sameSide_of_aux hx₁pos ha haD ?_ ?_ ?_⟩
      · intro b _ hb0
        have hle : (N : M) * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hNpos.le hb0
        rw [hx₁def]; linarith
      · intro b hbD hbpos hblt
        have hble : b ≤ bm := hbmmax b (by rw [hA₁def]; exact ⟨hbD, hbpos, hblt⟩)
        have hglt := gap_nmul_lt hgap hbmT hbmne hbmpos hbmlt N hN
        have hNb : (N : M) * b ≤ (N : M) * bm := mul_le_mul_of_nonneg_left hble hNpos.le
        have hlt : (N : M) * bm < ((2 * N : ℕ) : M) * bm := by
          have h : (N : M) < ((2 * N : ℕ) : M) := by push_cast; linarith
          exact mul_lt_mul_of_pos_right h hbmpos
        rw [hx₁def]
        exact ⟨by linarith, by linarith⟩
      · intro b hbD hab
        have hbne : b ≠ 0 := ne_of_gt (lt_trans ha hab)
        have hgt := gap_nmul_gt hgap (hDsubT b hbD) hbne ha hab N hN
        have hglt := gap_nmul_lt hgap hbmT hbmne hbmpos hbmlt (2 * N * N) (by positivity)
        have hcast : (N : M) * x₁ = ((2 * N * N : ℕ) : M) * bm := by
          rw [hx₁def]; push_cast; ring
        exact ⟨by rw [hcast]; linarith, hgt⟩
    · by_cases hne₂ : A₂.Nonempty
      · -- `bp = min(D ∩ (a,∞))` exists
        obtain ⟨bp, hbpA₂, hbpmin⟩ := Set.exists_min_image A₂ id hA₂fin hne₂
        rw [hA₂def] at hbpA₂
        obtain ⟨hbpB, hbpgt⟩ := hbpA₂
        have hbpT : bp ∈ T := hDsubT bp hbpB
        have hbppos : 0 < bp := lt_trans ha hbpgt
        set x₁ : M := bp / ((2 * N : ℕ) : M) with hx₁def
        have h2Npos : (0 : M) < ((2 * N : ℕ) : M) := by
          exact_mod_cast Nat.mul_pos (by norm_num) hN
        have h2Nne : ((2 * N : ℕ) : M) ≠ 0 := ne_of_gt h2Npos
        have hx₁T : x₁ ∈ T :=
          div_mem_T hTdcl hbpT (natCast_mem_T hTdcl (2 * N)) h2Nne
        have hx₁pos : 0 < x₁ := div_pos hbppos h2Npos
        refine ⟨x₁, hx₁T, hx₁pos, sameSide_of_aux hx₁pos ha haD ?_ ?_ ?_⟩
        · intro b _ hb0
          have hle : (N : M) * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hNpos.le hb0
          linarith
        · intro b hbD hbpos hblt
          exact absurd ⟨b, by rw [hA₁def]; exact ⟨hbD, hbpos, hblt⟩⟩ hne₁
        · intro b hbD hab
          have hbne : b ≠ 0 := ne_of_gt (lt_trans ha hab)
          have hgt := gap_nmul_gt hgap (hDsubT b hbD) hbne ha hab N hN
          have hbple : bp ≤ b := hbpmin b (by rw [hA₂def]; exact ⟨hbD, hab⟩)
          have hNx : (N : M) * x₁ = bp / 2 := by
            rw [hx₁def, mul_div_assoc']
            field_simp
            push_cast
            ring
          exact ⟨by rw [hNx]; linarith, hgt⟩
      · -- no breakpoint in `(0,a)` or `(a,∞)`: `x₁ = 1` works
        have hle0 : (1 : M) ≤ ((2 : ℕ) : M) := by norm_num
        refine ⟨1, one_mem_T hTdcl, one_pos, sameSide_of_aux one_pos ha haD ?_ ?_ ?_⟩
        · intro b _ hb0
          have hle : (N : M) * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hNpos.le hb0
          linarith
        · intro b hbD hbpos hblt
          exact absurd ⟨b, by rw [hA₁def]; exact ⟨hbD, hbpos, hblt⟩⟩ hne₁
        · intro b hbD hab
          exact absurd ⟨b, by rw [hA₂def]; exact ⟨hbD, hab⟩⟩ hne₂
  obtain ⟨x₁, hx₁T, hx₁pos, hx₁same⟩ := hx₁ex
  -- 6. the ULPM clauses at `(x₁, a)`
  obtain ⟨hdom, hrat⟩ := hD' x₁ a hx₁pos ha hx₁same
  have hzY : Fin.cons a (Fin.cons z c) ∈ Y := (hYfib a z).mpr ⟨hza, hZfib⟩
  obtain ⟨y₁, hy₁Y⟩ := hdom.mpr ⟨z, hzY⟩
  have hy₁T : y₁ ∈ T := by
    have hpre : ((∅ : Set M) ∪ {x₁}).Definable LRc
        {w : Fin (k + 1) → M | Fin.cons x₁ w ∈ Y} :=
      Work.WilC4g.definable_prepend (A := (∅ : Set M)) hYdef x₁
    have hfib := Work.WilC4g.definable_fibre_cons (A := (∅ : Set M) ∪ {x₁}) hpre c
    have hres : T.Definable₁ LRc {y : M | Fin.cons x₁ (Fin.cons y c) ∈ Y} :=
      hfib.mono (by
        rintro x ((hx | hx) | ⟨i, rfl⟩)
        · exact absurd hx (Set.notMem_empty x)
        · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hx₁T
        · exact hcT i)
    have hsing : {y : M | Fin.cons x₁ (Fin.cons y c) ∈ Y} = {y₁} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun hy => hYfun c x₁ y y₁ hy hy₁Y, fun hy => hy ▸ hy₁Y⟩
    exact (hTdcl y₁).mp (definableElt_of_singleton hres hsing)
  obtain ⟨q, _hqQs, t₁, t₂, hRpow₁, hRpow₂, hineq₁, hineq₂⟩ := hrat y₁ z hy₁Y hzY
  -- 7. the `IsRpow` data
  have hRpow₁' : IsRpow x₁ ((q.num : ℚ) / (q.den : ℚ)) t₁ := by
    rw [← Rat.num_div_den q] at hRpow₁; exact hRpow₁
  have hRpow₂' : IsRpow a ((q.num : ℚ) / (q.den : ℚ)) t₂ := by
    rw [← Rat.num_div_den q] at hRpow₂; exact hRpow₂
  obtain ⟨ht₁pow, ht₁nn⟩ :=
    (isRpow_canon (x := x₁) (t := t₁) q.den_pos hx₁pos).mp hRpow₁'
  obtain ⟨ht₂pow, ht₂nn⟩ :=
    (isRpow_canon (x := a) (t := t₂) q.den_pos ha).mp hRpow₂'
  have ht₁ne : t₁ ≠ 0 := fun h0 => (zpow_ne_zero q.num (ne_of_gt hx₁pos))
    (by rw [← ht₁pow, h0, zero_pow q.den_pos.ne'])
  have ht₂ne : t₂ ≠ 0 := fun h0 => (zpow_ne_zero q.num (ne_of_gt ha))
    (by rw [← ht₂pow, h0, zero_pow q.den_pos.ne'])
  have ht₁pos : 0 < t₁ := by
    rcases ht₁nn with h | ⟨w, hw, hw2⟩
    · exact absurd h ht₁ne
    · rw [← hw2]; exact sq_pos_of_ne_zero hw
  have ht₂pos : 0 < t₂ := by
    rcases ht₂nn with h | ⟨w, hw, hw2⟩
    · exact absurd h ht₂ne
    · rw [← hw2]; exact sq_pos_of_ne_zero hw
  have hy₁ne : y₁ ≠ 0 := by
    intro h0
    have hle : |z| * t₁ ≤ 0 := by
      have h := hineq₁
      simp only [h0, abs_zero, zero_mul, mul_zero] at h
      exact h
    have hzero : |z| * t₁ = 0 := le_antisymm hle (by positivity)
    rcases mul_eq_zero.mp hzero with h | h
    · exact hzne (abs_eq_zero.mp h)
    · exact absurd h (ne_of_gt ht₁pos)
  -- 8. the ratio `z t₁/(y₁ t₂)` is a unit
  set u : M := z * t₁ / (y₁ * t₂) with hudef
  have hApos : (0 : M) < |z| * t₁ := mul_pos (abs_pos.mpr hzne) ht₁pos
  have hBpos : (0 : M) < |y₁| * t₂ := mul_pos (abs_pos.mpr hy₁ne) ht₂pos
  have huabs : |u| = (|z| * t₁) / (|y₁| * t₂) := by
    rw [hudef, abs_div, abs_mul, abs_mul, abs_of_pos ht₁pos, abs_of_pos ht₂pos]
  have hu_unit : IsUnitVal u := by
    have hle : |u| ≤ (N : M) := by
      rw [huabs, div_le_iff₀ hBpos]; linarith
    have hinv : (N : M)⁻¹ ≤ |u| := by
      rw [huabs, le_div_iff₀ hBpos]
      have h : (N : M)⁻¹ * (|y₁| * t₂) ≤ |z| * t₁ := by
        have h1 : (N : M)⁻¹ * ((N : M) * (|z| * t₁)) = |z| * t₁ := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hNpos), one_mul]
        calc (N : M)⁻¹ * (|y₁| * t₂) ≤ (N : M)⁻¹ * ((N : M) * (|z| * t₁)) :=
              mul_le_mul_of_nonneg_left hineq₂ (by positivity)
          _ = |z| * t₁ := h1
      exact h
    refine ⟨N, ?_, ?_⟩
    · have hmono : (((N : ℕ) : M) + 1)⁻¹ ≤ (N : M)⁻¹ := by
        rw [inv_le_inv₀ (by positivity) hNpos]; linarith
      linarith
    · linarith
  -- 9. feed the ratio into the conclusion
  set α : M := y₁ ^ q.den / x₁ ^ q.num with hαdef
  have hxpow_ne : x₁ ^ q.num ≠ 0 := zpow_ne_zero q.num (ne_of_gt hx₁pos)
  have hαT : α ∈ T :=
    div_mem_T hTdcl (pow_mem_T hTdcl hy₁T q.den)
      (zpow_mem_T hTdcl hx₁T (ne_of_gt hx₁pos) q.num) hxpow_ne
  have hαne : α ≠ 0 := div_ne_zero (pow_ne_zero _ hy₁ne) hxpow_ne
  refine ⟨q.num, q.den, q.den_pos, α, hαT, hαne, ?_⟩
  have hu_pow : u ^ q.den = z ^ q.den / (α * a ^ q.num) := by
    have h1 : u ^ q.den = z ^ q.den * x₁ ^ q.num / (y₁ ^ q.den * a ^ q.num) := by
      rw [hudef, div_pow, mul_pow, mul_pow, ht₁pow, ht₂pow]
    rw [h1, hαdef]
    first | (field_simp; ring) | field_simp
  rw [← hu_pow]
  simpa [zpow_natCast] using unitVal_zpow hu_unit (q.den : ℤ)

end Work.WilC4
