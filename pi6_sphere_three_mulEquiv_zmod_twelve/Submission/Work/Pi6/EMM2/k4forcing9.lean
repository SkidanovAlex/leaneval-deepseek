import Mathlib
import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.K4Kit
import Submission.Work.Pi6.EMM2.K4F.transgression
import Submission.Work.Pi6.EMM2.K4F.sevenBound
import Submission.Work.Pi6.EMM2.K4F.eightBound

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

/-!
# Area EMM2 — the `K(ℤ/2,4)` forcing at threshold `10` (`Work.Pi6.EMM2.k4forcing9`)

For a range model `X` of `K(ℤ/2,4)` through degree `N ≥ 10` we prove
`dim H⁷(X;𝔽₂) ≤ 2` and `dim H⁸(X;𝔽₂) ≤ 2`, which are the third conjunct of `Work.Pi6.EMMod2`.

Everything happens in the mod-2 Serre spectral sequence `S` of the path–loop fibration
`ΩX → PX → X` (contractible total space, fibre the `K(ℤ/2,3)`-model `ΩX`) in total degrees `≤ 8`
(the fibre is known through `N - 1 ≥ 9`, so the finiteness hypotheses of `MSSHolds` are available
with `N = 8`).

* Degree `7`: the telescoped row-`0` bound (`Work.Pi6.EMM2.finrank_row0_bound`) gives
  `dim H⁷(X) ≤ dim H⁶(ΩX) ≤ 2`, all other sources on the diagonal vanishing.
* Degree `8`: the only differentials into `(8,0)` are `d₄` from `(4,3) = H⁴(X) ⊗ H³(ΩX)` and `d₈`
  from `(0,7) = H⁷(ΩX)`, so it suffices to bound the latter by `1`.  That is the crux: the class
  `p = v · w ∈ E₂^{4,4}` (product of the `e₂`-classes of `x₄ ⊗ 1` and `1 ⊗ y₄`) is nonzero, is a
  cycle up to page `4`, and its image `p₅ ∈ E₅^{4,4}` must vanish: otherwise `d₅ p₅ ≠ 0` (because
  `E₁₀^{4,4} = 0` and the only differential out of `(4,4)` in range is `d₅`), while
  `d₅ p₅ = ±(d₅ v₅)·w₅ = b₅·w₅ = 0` — the last equality because `w₄` is a transgression value
  (`c · w₄ = d₄ u`), so `w₄` is a boundary on `E₄` and its product with any row class dies in
  `E₅^{9,0}`.
-/

namespace Work.Pi6.EMM2

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝕜 : Type} [Field 𝕜]

/-! ## Auxiliary lemmas about the pages -/

/-- The differential applied to a class vanishes when its target does. -/
theorem k4_d_apply_eq_zero {𝕜 : Type} [Field 𝕜] (S : CohSS 𝕜) {r : ℕ} {a b : ℤ × ℤ}
    (h : IsZero (S.E r b)) (x : S.E r a) : (S.d r a b).hom x = 0 := by
  rw [S.d_eq_zero_of_isZero h]
  simp

/-- `E_r^{s,q} = 0` when the base group `H^s(B)` vanishes. -/
theorem k4_isZero_E_left {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (S : CohSS 𝕜) (hS : IsSerreMSS S p e₀ N)
    {s q r : ℕ} (hr : 2 ≤ r) (hs : s ≤ N) (hq : q ≤ N) (h : IsZero (Coh 𝕜 B s)) :
    IsZero (S.E r ((s : ℤ), (q : ℤ))) :=
  k4_isZero_E_of_isZero_E2 S (k4_isZero_E2_left (S := S) (p := p) (e₀ := e₀) (N := N)
    (hS := hS) (hs := hs) (hq := hq) (h := h)) hr

/-- `E_r^{s,q} = 0` when the fibre group `H^q(F)` vanishes. -/
theorem k4_isZero_E_right {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (S : CohSS 𝕜) (hS : IsSerreMSS S p e₀ N)
    {s q r : ℕ} (hr : 2 ≤ r) (hs : s ≤ N) (hq : q ≤ N) (h : IsZero (Coh 𝕜 (Fib p e₀) q)) :
    IsZero (S.E r ((s : ℤ), (q : ℤ))) :=
  k4_isZero_E_of_isZero_E2 S (k4_isZero_E2_right (S := S) (p := p) (e₀ := e₀) (N := N)
    (hS := hS) (hs := hs) (hq := hq) (h := h)) hr

/-- A class of `E_r^a` that is a cycle and is not hit is nonzero on the next page. -/
theorem k4_proj_ne_zero {𝕜 : Type} [Field 𝕜] (S : CohSS 𝕜) {r : ℕ} (hr : 2 ≤ r) (a : ℤ × ℤ) {x : S.E r a}
    (hcyc : (S.d r a (a + vr r)).hom x = 0) (hx : x ≠ 0)
    (hsrc : IsZero (S.E r (a - vr r))) :
    S.proj r a ⟨x, hcyc⟩ ≠ 0 := by
  intro hzero
  have hmem : x ∈ LinearMap.range (S.d r (a - vr r) a).hom :=
    (S.proj_ker r a hr ⟨x, hcyc⟩).mp hzero
  obtain ⟨z, hz⟩ := hmem
  haveI : Subsingleton (S.E r (a - vr r)) := ModuleCat.subsingleton_of_isZero hsrc
  rw [Subsingleton.elim z 0, map_zero] at hz
  exact hx hz.symm

/-- The dimension of `E_{r+1}^a` is at most the dimension of the cycles of `E_r^a`. -/
theorem k4_finrank_next_le_ker {𝕜 : Type} [Field 𝕜] (S : CohSS 𝕜) {r : ℕ} (hr : 2 ≤ r) (a : ℤ × ℤ) (hfin : FiniteDimensional 𝕜 (S.E r a)) :
    Module.finrank 𝕜 (S.E (r + 1) a) ≤
      Module.finrank 𝕜 ↥(LinearMap.ker (S.d r a (a + vr r)).hom) := by
  haveI := hfin
  have hP := LinearMap.finrank_range_add_finrank_ker (S.proj r a)
  have htop : LinearMap.range (S.proj r a) = ⊤ :=
    LinearMap.range_eq_top.mpr (S.proj_surj r a hr)
  have hfr : Module.finrank 𝕜 ↥(LinearMap.range (S.proj r a)) =
      Module.finrank 𝕜 (S.E (r + 1) a) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ htop ≪≫ₗ Submodule.topEquiv)
  omega

/-- A cast along an equality of natural numbers preserves (non)vanishing. -/
theorem k4_cast_ne_zero {Y : Type} [TopologicalSpace Y] {n m : ℕ} (h : n = m)
    {x : Coh 𝕜 Y n} : (h ▸ x : Coh 𝕜 Y m) ≠ 0 ↔ x ≠ 0 := by
  cases h
  rfl

/-- The page terms agree for equal (in particular definitionally equal) bidegrees. -/
theorem k4_E_eq {𝕜 : Type} [Field 𝕜] (S : CohSS 𝕜) (r : ℕ) (a b : ℤ × ℤ) (h : a = b) :
    S.E r a = S.E r b :=
  congrArg (S.E r) h

/-- `E₂^{s,q} = 0` when the base group `H^s(B)` is a subsingleton (abstract form: the instance
search for the tensor product is done with `B` a variable). -/
theorem k4_isZero_E2_left' {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (N : ℕ) (S : CohSS 𝕜) (hS : IsSerreMSS S p e₀ N)
    {s q : ℕ} (hs : s ≤ N) (hq : q ≤ N) (hsub : Subsingleton (Coh 𝕜 B s)) :
    IsZero (S.E 2 ((s : ℤ), (q : ℤ))) := by
  obtain ⟨e2, _⟩ := hS
  haveI := hsub
  haveI : Subsingleton (TensorProduct 𝕜 (Coh 𝕜 B s) (Coh 𝕜 (Fib p e₀) q)) := inferInstance
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) (e2 s q hs hq)

/-- Finiteness of the pages, inherited from page `2` by surjectivity of the projections. -/
theorem k4_finiteDimensional_E {𝕜 : Type} [Field 𝕜] (S : CohSS 𝕜) {a : ℤ × ℤ} (h2 : FiniteDimensional 𝕜 (S.E 2 a)) :
    ∀ k : ℕ, FiniteDimensional 𝕜 (S.E (k + 2) a) := by
  intro k
  induction k with
  | zero => simpa using h2
  | succ k ih =>
      haveI := ih
      exact FiniteDimensional.of_surjective (S.proj (k + 2) a)
        (S.proj_surj (k + 2) a (by omega))

/-- Monotonicity of the dimension along the pages. -/
theorem k4_finrank_mono {𝕜 : Type} [Field 𝕜] (S : CohSS 𝕜) (a : ℤ × ℤ) (r : ℕ) (hr : 2 ≤ r) :
    ∀ t : ℕ,
      (∀ k : ℕ, r ≤ k → k ≤ r + t → FiniteDimensional 𝕜 (S.E k a)) →
      Module.finrank 𝕜 (S.E (r + t) a) ≤ Module.finrank 𝕜 (S.E r a) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
      intro hfin
      have h1 : Module.finrank 𝕜 (S.E (r + t) a) ≤ Module.finrank 𝕜 (S.E r a) :=
        ih (fun k hk1 hk2 => hfin k hk1 (by omega))
      have h2 : Module.finrank 𝕜 (S.E (r + t + 1) a) ≤ Module.finrank 𝕜 (S.E (r + t) a) :=
        S.finrank_succ_le (r := r + t) (by omega) a (hfin (r + t) (by omega) (by omega))
      rw [show r + (t + 1) = r + t + 1 from by omega]
      exact h2.trans h1

/-- **A class of `E₄^{4,0}` that is a transgression value is a boundary.**  Hence its product with
any class of the row `q = 5` vanishes on `E₅^{9,0}`. -/
theorem k4_rowColProduct {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (e₀ : E) (N : ℕ) (S : CohSS (ZMod 2)) (hS : IsSerreMSS S p e₀ N)
    (w4 : S.E 4 ((4 : ℤ), (0 : ℤ)))
    (hcyc : (S.d 4 ((4 : ℤ), (0 : ℤ)) (((4 : ℤ), (0 : ℤ)) + vr 4)).hom w4 = 0)
    (u : S.E 4 ((0 : ℤ), (3 : ℤ))) (c : ZMod 2) (hc : c ≠ 0)
    (hu : (S.d 4 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 4)).hom u = c • w4) :
    ∀ b5 : S.E 5 ((5 : ℤ), (0 : ℤ)),
      S.mul 5 ((5 : ℤ), (0 : ℤ)) ((4 : ℤ), (0 : ℤ)) (((5 + 4 : ℕ) : ℤ), ((0 + 0 : ℕ) : ℤ))
        (by ext <;> simp) b5 (S.proj 4 ((4 : ℤ), (0 : ℤ)) ⟨w4, hcyc⟩) = 0 := by
  intro b5
  have hw4range : w4 ∈ LinearMap.range
      (S.d 4 (((4 : ℤ), (0 : ℤ)) - vr 4) ((4 : ℤ), (0 : ℤ))).hom := by
    refine ⟨c⁻¹ • u, ?_⟩
    have h1 : (S.d 4 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 4)).hom (c⁻¹ • u) = w4 := by
      rw [map_smul, hu]
      exact inv_smul_smul₀ hc w4
    exact h1
  have hproj0 : S.proj 4 ((4 : ℤ), (0 : ℤ)) ⟨w4, hcyc⟩ = 0 :=
    (S.proj_ker 4 ((4 : ℤ), (0 : ℤ)) (by norm_num) ⟨w4, hcyc⟩).mpr hw4range
  rw [hproj0]
  simp

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- **The crux of the `K(ℤ/2,4)` forcing.**  In the Serre spectral sequence of `p` (with `E` acyclic
through degree `8`), the column `E₂^{0,7}` loses a dimension before page `8`: `dim E₈^{0,7} ≤ 1`. -/
theorem k4_crux {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (N : ℕ) (S : CohSS (ZMod 2)) (hS : IsSerreMSS S p e₀ N) (hN : 8 ≤ N)
    (hBfin : ∀ s : ℕ, s ≤ N → FiniteDimensional (ZMod 2) (Coh (ZMod 2) B s))
    (hFfin : ∀ q : ℕ, q ≤ N → FiniteDimensional (ZMod 2) (Coh (ZMod 2) (Fib p e₀) q))
    (hB0 : Module.finrank (ZMod 2) (Coh (ZMod 2) B 0) = 1)
    (hF0 : Module.finrank (ZMod 2) (Coh (ZMod 2) (Fib p e₀) 0) = 1)
    (hB4 : Module.finrank (ZMod 2) (Coh (ZMod 2) B 4) = 1)
    (hF3 : Module.finrank (ZMod 2) (Coh (ZMod 2) (Fib p e₀) 3) = 1)
    (hF4 : Module.finrank (ZMod 2) (Coh (ZMod 2) (Fib p e₀) 4) = 1)
    (hF7 : Module.finrank (ZMod 2) (Coh (ZMod 2) (Fib p e₀) 7) ≤ 2)
    (hB1 : IsZero (Coh (ZMod 2) B 1)) (hB2 : IsZero (Coh (ZMod 2) B 2))
    (hB3 : IsZero (Coh (ZMod 2) B 3))
    (hF1 : IsZero (Coh (ZMod 2) (Fib p e₀) 1)) (hF2 : IsZero (Coh (ZMod 2) (Fib p e₀) 2))
    (hE8 : IsZero (Coh (ZMod 2) E 8))
    (u : S.E 4 ((0 : ℤ), (3 : ℤ)))
    (hu : (S.d 4 ((0 : ℤ), (3 : ℤ)) ((4 : ℤ), (0 : ℤ))).hom u ≠ 0)
    (hco : CupOneStatement) :
    Module.finrank (ZMod 2) (S.E 8 ((0 : ℤ), (7 : ℤ))) ≤ 1 := by
  have hSS := hS
  obtain ⟨e2, hmul, hconv0, hconv, hbot, hcol⟩ := hS
  have hB0ne : one (ZMod 2) B ≠ 0 := k4_one_ne_zero hB0
  have hF0ne : one (ZMod 2) (Fib p e₀) ≠ 0 := k4_one_ne_zero hF0
  obtain ⟨x4, hx4⟩ := k4_exists_ne_zero (𝕜 := ZMod 2) hB4
  obtain ⟨y4, hy4⟩ := k4_exists_ne_zero (𝕜 := ZMod 2) hF4
  -- ## the two `E₂`-classes and their product
  let v : S.E 2 ((0 : ℤ), (4 : ℤ)) :=
    (e2 0 4 (by omega) (by omega)).inv.hom (one (ZMod 2) B ⊗ₜ[ZMod 2] y4)
  let w : S.E 2 ((4 : ℤ), (0 : ℤ)) :=
    (e2 4 0 (by omega) (by omega)).inv.hom (x4 ⊗ₜ[ZMod 2] one (ZMod 2) (Fib p e₀))
  have hv : v ≠ 0 :=
    k4_e2_inv_tmul_ne_zero (p := p) (e₀ := e₀) (S := S)
      (e2 := e2 0 4 (by omega) (by omega)) hB0ne hy4
  have hw : w ≠ 0 :=
    k4_e2_inv_tmul_ne_zero (p := p) (e₀ := e₀) (S := S)
      (e2 := e2 4 0 (by omega) (by omega)) hx4 hF0ne
  let prod : S.E 2 ((4 : ℤ), (4 : ℤ)) :=
    S.mul 2 ((0 : ℤ), (4 : ℤ)) ((4 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))
      (by ext <;> simp) v w
  have hprod : prod ≠ 0 := by
    have hcl := hmul 0 4 4 0 (one (ZMod 2) B) y4 x4 (one (ZMod 2) (Fib p e₀))
      (by omega) (by omega)
    have hcupB : cup (ZMod 2) B 0 4 (one (ZMod 2) B) x4 = (Nat.zero_add 4).symm ▸ x4 := by
      show Work.Cohomology.cupH' (ZMod 2) (TopCat.toSSet.obj (TopCat.of B)) 0 4
        (Work.Cohomology.oneH (ZMod 2) (TopCat.toSSet.obj (TopCat.of B))) x4 = _
      exact Work.Cohomology.cupH'_one_left (ZMod 2) (TopCat.toSSet.obj (TopCat.of B)) 4 x4
    have hcupF : cup (ZMod 2) (Fib p e₀) 4 0 y4 (one (ZMod 2) (Fib p e₀)) = y4 := by
      show Work.Cohomology.cupH' (ZMod 2) (TopCat.toSSet.obj (TopCat.of (Fib p e₀))) 4 0 y4
        (Work.Cohomology.oneH (ZMod 2) (TopCat.toSSet.obj (TopCat.of (Fib p e₀)))) = _
      exact Work.Cohomology.cupH'_one_right (ZMod 2) (TopCat.toSSet.obj (TopCat.of (Fib p e₀))) 4 y4
    rw [hcupB, hcupF, show ((-1 : ZMod 2) ^ (4 * 4)) = 1 from by decide, one_smul] at hcl
    have hx4' : ((Nat.zero_add 4).symm ▸ x4 : Coh (ZMod 2) B (0 + 4)) ≠ 0 :=
      (k4_cast_ne_zero (𝕜 := ZMod 2) (Y := B) (n := 4) (m := 0 + 4) (x := x4)
        (Nat.zero_add 4).symm).mpr hx4
    have hne : (e2 (0 + 4) (4 + 0) (by omega) (by omega)).inv.hom
        (((Nat.zero_add 4).symm ▸ x4 : Coh (ZMod 2) B (0 + 4)) ⊗ₜ[ZMod 2] y4) ≠ 0 := by
      have htm : ((Nat.zero_add 4).symm ▸ x4 : Coh (ZMod 2) B (0 + 4)) ⊗ₜ[ZMod 2] y4 ≠ 0 :=
        tmul_ne_zero_of_ne_zero hx4' hy4
      intro h0
      refine htm ?_
      rw [← k4_iso_hom_inv_hom_apply (e2 (0 + 4) (4 + 0) (by omega) (by omega))
        (((Nat.zero_add 4).symm ▸ x4 : Coh (ZMod 2) B (0 + 4)) ⊗ₜ[ZMod 2] y4), h0]
      simp
    intro hzero
    exact hne (by rw [← hcl]; exact hzero)
  -- ## the product is a cycle through page `4`
  have hdv2 : (S.d 2 ((0 : ℤ), (4 : ℤ)) (((0 : ℤ), (4 : ℤ)) + vr 2)).hom v = 0 := by
    refine k4_d_apply_eq_zero S ?_ v
    rw [show ((0 : ℤ), (4 : ℤ)) + vr 2 = ((2 : ℤ), (3 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_left (p := p) (e₀ := e₀) (N := N) (S := S) (hS := hSS)
      (r := 2) (s := 2) (q := 3) (by norm_num) (by omega) (by omega) hB2
  have hdw2 : (S.d 2 ((4 : ℤ), (0 : ℤ)) (((4 : ℤ), (0 : ℤ)) + vr 2)).hom w = 0 :=
    k4_d_apply_eq_zero S (S.quad 2 (((4 : ℤ), (0 : ℤ)) + vr 2) (Or.inr (by decide))) w
  have hdprod2 : (S.d 2 ((4 : ℤ), (4 : ℤ)) (((4 : ℤ), (4 : ℤ)) + vr 2)).hom prod = 0 := by
    rw [show prod = S.mul 2 ((0 : ℤ), (4 : ℤ)) ((4 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))
      (by ext <;> simp) v w from rfl]
    rw [S.leibniz 2 ((0 : ℤ), (4 : ℤ)) ((4 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))
      (by ext <;> simp) v w (by norm_num), hdv2, hdw2]
    simp
  -- ## nothing hits `(4,4)` (resp. `(4,0)`) on the first pages
  have hsrc25 : IsZero (S.E 2 (((4 : ℤ), (4 : ℤ)) - vr 2)) := by
    rw [show ((4 : ℤ), (4 : ℤ)) - vr 2 = ((2 : ℤ), (5 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_left (p := p) (e₀ := e₀) (N := N) (S := S) (hS := hSS)
      (r := 2) (s := 2) (q := 5) (by norm_num) (by omega) (by omega) hB2
  have hsrc16 : IsZero (S.E 3 (((4 : ℤ), (4 : ℤ)) - vr 3)) := by
    rw [show ((4 : ℤ), (4 : ℤ)) - vr 3 = ((1 : ℤ), (6 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_left (p := p) (e₀ := e₀) (N := N) (S := S) (hS := hSS)
      (r := 3) (s := 1) (q := 6) (by norm_num) (by omega) (by omega) hB1
  have hsrcw2 : IsZero (S.E 2 (((4 : ℤ), (0 : ℤ)) - vr 2)) := by
    rw [show ((4 : ℤ), (0 : ℤ)) - vr 2 = ((2 : ℤ), (1 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_right (p := p) (e₀ := e₀) (N := N) (S := S) (hS := hSS)
      (r := 2) (s := 2) (q := 1) (by norm_num) (by omega) (by omega) hF1
  have hsrcw3 : IsZero (S.E 3 (((4 : ℤ), (0 : ℤ)) - vr 3)) := by
    rw [show ((4 : ℤ), (0 : ℤ)) - vr 3 = ((1 : ℤ), (2 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_left (p := p) (e₀ := e₀) (N := N) (S := S) (hS := hSS)
      (r := 3) (s := 1) (q := 2) (by norm_num) (by omega) (by omega) hB1
  -- ## the images on the pages `3` and `4`
  let v2 : S.E 3 ((0 : ℤ), (4 : ℤ)) := S.proj 2 ((0 : ℤ), (4 : ℤ)) ⟨v, hdv2⟩
  let w2 : S.E 3 ((4 : ℤ), (0 : ℤ)) := S.proj 2 ((4 : ℤ), (0 : ℤ)) ⟨w, hdw2⟩
  let P2 : S.E 3 ((4 : ℤ), (4 : ℤ)) := S.proj 2 ((4 : ℤ), (4 : ℤ)) ⟨prod, hdprod2⟩
  have hP2ne : P2 ≠ 0 :=
    k4_proj_ne_zero S (r := 2) (by norm_num) ((4 : ℤ), (4 : ℤ)) hdprod2 hprod hsrc25
  have hw2ne : w2 ≠ 0 :=
    k4_proj_ne_zero S (r := 2) (by norm_num) ((4 : ℤ), (0 : ℤ)) hdw2 hw hsrcw2
  have hP2prod : P2 = S.mul 3 ((0 : ℤ), (4 : ℤ)) ((4 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))
      (by ext <;> simp) v2 w2 :=
    S.proj_mul 2 ((0 : ℤ), (4 : ℤ)) ((4 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))
      (by ext <;> simp) ⟨v, hdv2⟩ ⟨w, hdw2⟩ ⟨prod, hdprod2⟩ (by norm_num) rfl
  have hdv3 : (S.d 3 ((0 : ℤ), (4 : ℤ)) (((0 : ℤ), (4 : ℤ)) + vr 3)).hom v2 = 0 := by
    refine k4_d_apply_eq_zero S ?_ v2
    rw [show ((0 : ℤ), (4 : ℤ)) + vr 3 = ((3 : ℤ), (2 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_left (p := p) (e₀ := e₀) (N := N) (S := S) (hS := hSS)
      (r := 3) (s := 3) (q := 2) (by norm_num) (by omega) (by omega) hB3
  have hdw3 : (S.d 3 ((4 : ℤ), (0 : ℤ)) (((4 : ℤ), (0 : ℤ)) + vr 3)).hom w2 = 0 :=
    k4_d_apply_eq_zero S (S.quad 3 (((4 : ℤ), (0 : ℤ)) + vr 3) (Or.inr (by decide))) w2
  have hdP3 : (S.d 3 ((4 : ℤ), (4 : ℤ)) (((4 : ℤ), (4 : ℤ)) + vr 3)).hom P2 = 0 := by
    rw [hP2prod]
    rw [S.leibniz 3 ((0 : ℤ), (4 : ℤ)) ((4 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))
      (by ext <;> simp) v2 w2 (by norm_num), hdv3, hdw3]
    simp
  let v3 : S.E 4 ((0 : ℤ), (4 : ℤ)) := S.proj 3 ((0 : ℤ), (4 : ℤ)) ⟨v2, hdv3⟩
  let w3 : S.E 4 ((4 : ℤ), (0 : ℤ)) := S.proj 3 ((4 : ℤ), (0 : ℤ)) ⟨w2, hdw3⟩
  let P3 : S.E 4 ((4 : ℤ), (4 : ℤ)) := S.proj 3 ((4 : ℤ), (4 : ℤ)) ⟨P2, hdP3⟩
  have hP3ne : P3 ≠ 0 :=
    k4_proj_ne_zero S (r := 3) (by norm_num) ((4 : ℤ), (4 : ℤ)) hdP3 hP2ne hsrc16
  have hw3ne : w3 ≠ 0 :=
    k4_proj_ne_zero S (r := 3) (by norm_num) ((4 : ℤ), (0 : ℤ)) hdw3 hw2ne hsrcw3
  have hP3prod : P3 = S.mul 4 ((0 : ℤ), (4 : ℤ)) ((4 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))
      (by ext <;> simp) v3 w3 :=
    S.proj_mul 3 ((0 : ℤ), (4 : ℤ)) ((4 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))
      (by ext <;> simp) ⟨v2, hdv3⟩ ⟨w2, hdw3⟩ ⟨P2, hdP3⟩ (by norm_num) hP2prod
  -- ## finiteness of the pages used below
  haveI hB4fin : FiniteDimensional (ZMod 2) (Coh (ZMod 2) B 4) :=
    FiniteDimensional.of_finrank_pos (by rw [hB4]; norm_num)
  haveI hF0fin : FiniteDimensional (ZMod 2) (Coh (ZMod 2) (Fib p e₀) 0) :=
    FiniteDimensional.of_finrank_pos (by rw [hF0]; norm_num)
  have hfin2_40 : FiniteDimensional (ZMod 2) (S.E 2 ((4 : ℤ), (0 : ℤ))) :=
    Module.Finite.equiv (e2 4 0 (by omega) (by omega)).symm.toLinearEquiv
  have hfin4_40 : FiniteDimensional (ZMod 2) (S.E 4 ((4 : ℤ), (0 : ℤ))) :=
    k4_finiteDimensional_E S hfin2_40 2
  -- ## `d₄u` is a nonzero multiple of `w₃`
  have hdim40 : Module.finrank (ZMod 2) (S.E 4 ((4 : ℤ), (0 : ℤ))) = 1 := by
    have h2 : Module.finrank (ZMod 2) (S.E 2 ((4 : ℤ), (0 : ℤ))) = 1 := by
      rw [k4_E_eq S 2 ((4 : ℤ), (0 : ℤ)) (((4 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) (by rfl),
        e2_finrank S p e₀ N hSS 4 0 (by omega) (by omega), hB4, hF0, mul_one]
    have hm : Module.finrank (ZMod 2) (S.E 4 ((4 : ℤ), (0 : ℤ))) ≤ 1 := by
      have h := k4_finrank_mono S ((4 : ℤ), (0 : ℤ)) 2 (by norm_num) 2
        (fun k hk1 hk2 => by
          interval_cases k
          · exact hfin2_40
          · exact k4_finiteDimensional_E S hfin2_40 1
          · exact hfin4_40)
      rw [h2] at h
      exact h
    exact le_antisymm hm (k4_finrank_pos_of_ne_zero hw3ne)
  obtain ⟨c, hc, hcu⟩ : ∃ c : ZMod 2, c ≠ 0 ∧
      (S.d 4 ((0 : ℤ), (3 : ℤ)) ((4 : ℤ), (0 : ℤ))).hom u = c • w3 := by
    haveI := hfin4_40
    have hspan : Submodule.span (ZMod 2) ({w3} : Set (S.E 4 ((4 : ℤ), (0 : ℤ)))) = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [finrank_span_singleton hw3ne, hdim40]
    have hmem : (S.d 4 ((0 : ℤ), (3 : ℤ)) ((4 : ℤ), (0 : ℤ))).hom u ∈
        Submodule.span (ZMod 2) ({w3} : Set (S.E 4 ((4 : ℤ), (0 : ℤ)))) := by
      rw [hspan]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨c, fun hc0 => ?_, hc.symm⟩
    have hzero : (S.d 4 ((0 : ℤ), (3 : ℤ)) ((4 : ℤ), (0 : ℤ))).hom u = 0 := by
      rw [← hc, hc0, zero_smul]
    exact hu hzero
  -- ## the image on page `5`
  have hdv4 : (S.d 4 ((0 : ℤ), (4 : ℤ)) (((0 : ℤ), (4 : ℤ)) + vr 4)).hom v3 = 0 := by
    refine k4_d_apply_eq_zero S ?_ v3
    rw [show ((0 : ℤ), (4 : ℤ)) + vr 4 = ((4 : ℤ), (1 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_right (p := p) (e₀ := e₀) (N := N) (S := S) (hS := hSS)
      (r := 4) (s := 4) (q := 1) (by norm_num) (by omega) (by omega) hF1
  have hdw4 : (S.d 4 ((4 : ℤ), (0 : ℤ)) (((4 : ℤ), (0 : ℤ)) + vr 4)).hom w3 = 0 :=
    k4_d_apply_eq_zero S (S.quad 4 (((4 : ℤ), (0 : ℤ)) + vr 4) (Or.inr (by decide))) w3
  have hdP4 : (S.d 4 ((4 : ℤ), (4 : ℤ)) (((4 : ℤ), (4 : ℤ)) + vr 4)).hom P3 = 0 := by
    rw [hP3prod]
    rw [S.leibniz 4 ((0 : ℤ), (4 : ℤ)) ((4 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))
      (by ext <;> simp) v3 w3 (by norm_num), hdv4, hdw4]
    simp
  let v4 : S.E 5 ((0 : ℤ), (4 : ℤ)) := S.proj 4 ((0 : ℤ), (4 : ℤ)) ⟨v3, hdv4⟩
  let w4 : S.E 5 ((4 : ℤ), (0 : ℤ)) := S.proj 4 ((4 : ℤ), (0 : ℤ)) ⟨w3, hdw4⟩
  let P4 : S.E 5 ((4 : ℤ), (4 : ℤ)) := S.proj 4 ((4 : ℤ), (4 : ℤ)) ⟨P3, hdP4⟩
  have hP4prod : P4 = S.mul 5 ((0 : ℤ), (4 : ℤ)) ((4 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))
      (by ext <;> simp) v4 w4 :=
    S.proj_mul 4 ((0 : ℤ), (4 : ℤ)) ((4 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))
      (by ext <;> simp) ⟨v3, hdv4⟩ ⟨w3, hdw4⟩ ⟨P3, hdP4⟩ (by norm_num) hP3prod
  -- ## `E₁₀^{4,4} = 0`
  have hE10 : IsZero (S.E 10 ((4 : ℤ), (4 : ℤ))) :=
    hconv0 8 (by norm_num) (by omega) (ModuleCat.subsingleton_of_isZero hE8) 4 4 (by norm_num)
  -- ## the case analysis
  have hd4ne : ∃ z : S.E 4 ((0 : ℤ), (7 : ℤ)),
      (S.d 4 ((0 : ℤ), (7 : ℤ)) (((0 : ℤ), (7 : ℤ)) + vr 4)).hom z ≠ 0 := by
    by_cases hP4 : P4 = 0
    · have hmem : P3 ∈ LinearMap.range
          (S.d 4 (((4 : ℤ), (4 : ℤ)) - vr 4) ((4 : ℤ), (4 : ℤ))).hom :=
        (S.proj_ker 4 ((4 : ℤ), (4 : ℤ)) (by norm_num) ⟨P3, hdP4⟩).mp hP4
      obtain ⟨z, hz⟩ := hmem
      refine ⟨z, ?_⟩
      intro hz0
      have h1 : (S.d 4 (((4 : ℤ), (4 : ℤ)) - vr 4) ((4 : ℤ), (4 : ℤ))).hom z = 0 := hz0
      exact hP3ne (hz.symm.trans h1)
    · have hd5ne : (S.d 5 ((4 : ℤ), (4 : ℤ)) (((4 : ℤ), (4 : ℤ)) + vr 5)).hom P4 ≠ 0 := by
        intro h0
        have hsrc : ∀ k : ℕ, 5 ≤ k → IsZero (S.E k (((4 : ℤ), (4 : ℤ)) - vr k)) := by
          intro k hk
          refine S.quad k _ (Or.inl ?_)
          simp only [Prod.fst_sub, vr, Prod.fst_ofNat]
          omega
        have htgt : ∀ k : ℕ, 5 + 1 ≤ k → IsZero (S.E k (((4 : ℤ), (4 : ℤ)) + vr k)) := by
          intro k hk
          refine S.quad k _ (Or.inr ?_)
          simp only [Prod.snd_add, vr, Prod.snd_ofNat]
          omega
        obtain ⟨y, hy⟩ := S.exists_ne_zero_iterate (r := 5) (by norm_num) ((4 : ℤ), (4 : ℤ))
          P4 h0 hP4 hsrc htgt 5
        exact hy ((ModuleCat.subsingleton_of_isZero hE10).allEq y 0)
      have hd5val : (S.d 5 ((4 : ℤ), (4 : ℤ)) (((4 : ℤ), (4 : ℤ)) + vr 5)).hom P4 =
          S.mul 5 (((0 : ℤ), (4 : ℤ)) + vr 5) ((4 : ℤ), (0 : ℤ)) (((4 : ℤ), (4 : ℤ)) + vr 5)
            (by ext <;> norm_num [vr])
            ((S.d 5 ((0 : ℤ), (4 : ℤ)) (((0 : ℤ), (4 : ℤ)) + vr 5)).hom v4) w4 := by
        rw [hP4prod]
        rw [S.leibniz 5 ((0 : ℤ), (4 : ℤ)) ((4 : ℤ), (0 : ℤ)) ((4 : ℤ), (4 : ℤ))
          (by ext <;> simp) v4 w4 (by norm_num)]
        have hz : (S.d 5 ((4 : ℤ), (0 : ℤ)) (((4 : ℤ), (0 : ℤ)) + vr 5)).hom w4 = 0 :=
          k4_d_apply_eq_zero S (S.quad 5 (((4 : ℤ), (0 : ℤ)) + vr 5) (Or.inr (by decide))) w4
        rw [hz]
        simp
      have hvan : S.mul 5 (((0 : ℤ), (4 : ℤ)) + vr 5) ((4 : ℤ), (0 : ℤ))
          (((4 : ℤ), (4 : ℤ)) + vr 5) (by ext <;> norm_num [vr])
          ((S.d 5 ((0 : ℤ), (4 : ℤ)) (((0 : ℤ), (4 : ℤ)) + vr 5)).hom v4) w4 = 0 :=
        k4_rowColProduct p e₀ N S hSS w3 hdw4 u c hc hcu _
      exact absurd (hd5val.trans hvan) hd5ne
  -- ## rank–nullity
  obtain ⟨z, hz⟩ := hd4ne
  have hker : Module.finrank (ZMod 2) ↥(LinearMap.ker
      (S.d 4 ((0 : ℤ), (7 : ℤ)) (((0 : ℤ), (7 : ℤ)) + vr 4)).hom) ≤ 1 := by
    have h2 : Module.finrank (ZMod 2) (S.E 2 ((0 : ℤ), (7 : ℤ))) ≤ 2 := by
      rw [k4_E_eq S 2 ((0 : ℤ), (7 : ℤ)) (((0 : ℕ) : ℤ), ((7 : ℕ) : ℤ)) (by rfl),
        e2_finrank S p e₀ N hSS 0 7 (by omega) (by omega), hB0, one_mul]
      exact hF7
    haveI := hBfin 0 (by omega)
    haveI := hFfin 7 (by omega)
    have hfin2 : FiniteDimensional (ZMod 2) (S.E 2 ((0 : ℤ), (7 : ℤ))) :=
      Module.Finite.equiv (e2 0 7 (by omega) (by omega)).symm.toLinearEquiv
    have hfin4 : FiniteDimensional (ZMod 2) (S.E 4 ((0 : ℤ), (7 : ℤ))) :=
      k4_finiteDimensional_E S hfin2 2
    haveI := hfin4
    have hE4le : Module.finrank (ZMod 2) (S.E 4 ((0 : ℤ), (7 : ℤ))) ≤ 2 := by
      have h := k4_finrank_mono S ((0 : ℤ), (7 : ℤ)) 2 (by norm_num) 2
        (fun k hk1 hk2 => by
          interval_cases k
          · exact hfin2
          · exact k4_finiteDimensional_E S hfin2 1
          · exact hfin4)
      exact h.trans h2
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (S.d 4 ((0 : ℤ), (7 : ℤ)) (((0 : ℤ), (7 : ℤ)) + vr 4)).hom
    have hrange : 1 ≤ Module.finrank (ZMod 2) ↥(LinearMap.range
        (S.d 4 ((0 : ℤ), (7 : ℤ)) (((0 : ℤ), (7 : ℤ)) + vr 4)).hom) := by
      have hnt : Nontrivial ↥(LinearMap.range
          (S.d 4 ((0 : ℤ), (7 : ℤ)) (((0 : ℤ), (7 : ℤ)) + vr 4)).hom) :=
        ⟨⟨(S.d 4 ((0 : ℤ), (7 : ℤ)) (((0 : ℤ), (7 : ℤ)) + vr 4)).hom z, ⟨z, rfl⟩⟩, 0, by
          intro hEq
          have h2 := congrArg (fun w : ↥(LinearMap.range
            (S.d 4 ((0 : ℤ), (7 : ℤ)) (((0 : ℤ), (7 : ℤ)) + vr 4)).hom) =>
              (w : S.E 4 (((0 : ℤ), (7 : ℤ)) + vr 4))) hEq
          simp only [Submodule.coe_zero] at h2
          exact hz h2⟩
      exact Module.finrank_pos_iff.mpr hnt
    omega
  have h45 : Module.finrank (ZMod 2) (S.E 5 ((0 : ℤ), (7 : ℤ))) ≤
      Module.finrank (ZMod 2) ↥(LinearMap.ker
        (S.d 4 ((0 : ℤ), (7 : ℤ)) (((0 : ℤ), (7 : ℤ)) + vr 4)).hom) := by
    haveI := hBfin 0 (by omega)
    haveI := hFfin 7 (by omega)
    have hfin2 : FiniteDimensional (ZMod 2) (S.E 2 ((0 : ℤ), (7 : ℤ))) :=
      Module.Finite.equiv (e2 0 7 (by omega) (by omega)).symm.toLinearEquiv
    exact k4_finrank_next_le_ker S (by norm_num) _ (k4_finiteDimensional_E S hfin2 2)
  have h85 : Module.finrank (ZMod 2) (S.E 8 ((0 : ℤ), (7 : ℤ))) ≤
      Module.finrank (ZMod 2) (S.E 5 ((0 : ℤ), (7 : ℤ))) := by
    haveI := hBfin 0 (by omega)
    haveI := hFfin 7 (by omega)
    have hfin2 : FiniteDimensional (ZMod 2) (S.E 2 ((0 : ℤ), (7 : ℤ))) :=
      Module.Finite.equiv (e2 0 7 (by omega) (by omega)).symm.toLinearEquiv
    exact k4_finrank_mono S ((0 : ℤ), (7 : ℤ)) 5 (by norm_num) 3
      (fun k hk1 hk2 => by
        have h := k4_finiteDimensional_E S hfin2 (k - 2)
        rwa [Nat.sub_add_cancel (by omega : 2 ≤ k)] at h)
  omega


/-- **The `K(ℤ/2,4)` forcing at threshold `10`.** -/
theorem k4forcing9 : Work.Pi6.EMM2.K4FactsLowStatement := by
  intro hM hKZ hFT hLD h2f h2c hmc hco hPF hk2 hk3 X _inst x₀ N hN10 hX
  have hN8 : 8 ≤ N := by omega
  -- ## the path fibration
  obtain ⟨hcontr, hserre, hFibEM⟩ := hPF (A := ZMod 2) (m := 4) (M := N) (by norm_num) x₀ hX
  haveI : ContractibleSpace (k4PathSpace x₀) := hcontr
  have hE : ∀ n : ℕ, 1 ≤ n → n ≤ 8 → IsZero (Coh (ZMod 2) (k4PathSpace x₀) n) := by
    intro n hn h8
    have h := Work.Cohomology.contractible (ZMod 2) (TopCat.of (k4PathSpace x₀)) (n - 1)
    rwa [show n - 1 + 1 = n from by omega] at h
  -- ## low-degree facts
  obtain ⟨hSC, hX0, hXlow⟩ := hLD (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 4) (M := N)
    (by norm_num) (by omega) x₀ hX
  obtain ⟨-, hF0, hFlow⟩ := hLD (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 3) (M := N - 1)
    (by norm_num) (by omega) (X := k4LoopSpace x₀) (k4LoopBase x₀) hFibEM
  obtain ⟨hF3, hF4, hF5, hF6, hF7, hFsq⟩ :=
    hk3 hM hKZ hFT hLD h2f h2c hmc hco hPF hk2 (X := k4LoopSpace x₀) (x₀ := k4LoopBase x₀)
      (N := N - 1) (by omega) hFibEM
  have hB1 : IsZero (Coh (ZMod 2) X 1) := hXlow 1 (by norm_num) (by norm_num)
  have hB2 : IsZero (Coh (ZMod 2) X 2) := hXlow 2 (by norm_num) (by norm_num)
  have hB3 : IsZero (Coh (ZMod 2) X 3) := hXlow 3 (by norm_num) (by norm_num)
  have hF1 : IsZero (Coh (ZMod 2) (k4LoopSpace x₀) 1) := hFlow 1 (by norm_num) (by norm_num)
  have hF2 : IsZero (Coh (ZMod 2) (k4LoopSpace x₀) 2) := hFlow 2 (by norm_num) (by norm_num)
  -- ## finiteness
  have hBfin : ∀ s : ℕ, s ≤ N - 1 → FiniteDimensional (ZMod 2) (Coh (ZMod 2) X s) := by
    intro s hs
    refine hFT (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 4) (N := N - 1) (by norm_num)
      (X := X) x₀ ?_ s hs
    rw [show (N - 1) + 1 = N from by omega]
    exact hX
  have hFfin : ∀ q : ℕ, q ≤ 8 → FiniteDimensional (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) q) := by
    intro q hq
    refine hFT (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 3) (N := 8) (by norm_num)
      (X := k4LoopSpace x₀) (x := k4LoopBase x₀) ?_ q hq
    exact k4_isEMSpaceUpTo_mono (by norm_num) hFibEM (by omega)
  -- ## the spectral sequence through degree `8`
  obtain ⟨S, hS⟩ := hM (ZMod 2) (k4PathSpace x₀) X (k4PathFib x₀) (k4PathBase x₀) 8 hserre hSC
    (fun q hq => hFfin q hq) (fun s hs => hBfin s (by omega))
  have hSS := hS
  obtain ⟨e2, hmul, hconv0, hconv, hbot, hcol⟩ := hS
  -- ## the transgression
  obtain ⟨u, hu⟩ := K4F.transgression (k4PathFib x₀) (k4PathBase x₀) 8 S hSS (by norm_num) hX0 hF3 hB2 hB3
    hF1 hF2 (hE 3 (by norm_num) (by omega))
  -- ## `dim H⁴(X) = 1`
  have hb4le : Module.finrank (ZMod 2) (Coh (ZMod 2) X 4) ≤ 1 := by
    have h := finrank_row0_bound S (k4PathFib x₀) (k4PathBase x₀) 8 hSS
      (fun s hs => hBfin s (by omega)) (fun q hq => hFfin q hq) hF0 4 (by omega)
    rw [k4_finrank_eq_zero_of_isZero_cohom (𝕜 := ZMod 2) (hE 4 (by norm_num) (by omega)),
      zero_add] at h
    refine h.trans ?_
    have hterm : ∀ r ∈ Finset.range (4 - 1),
        Module.finrank (ZMod 2) (Coh (ZMod 2) X (4 - (r + 2))) *
          Module.finrank (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) (r + 1)) ≤
            if r = 2 then 1 else 0 := by
      intro r hr
      rw [Finset.mem_range] at hr
      interval_cases r
      · have hz : Module.finrank (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) (0 + 1)) = 0 := by
          rw [show 0 + 1 = 1 from by norm_num]
          exact k4_finrank_eq_zero_of_isZero_cohom hF1
        rw [hz, mul_zero]
        simp
      · have hz : Module.finrank (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) (1 + 1)) = 0 := by
          rw [show 1 + 1 = 2 from by norm_num]
          exact k4_finrank_eq_zero_of_isZero_cohom hF2
        rw [hz, mul_zero]
        simp
      · have h1 : Module.finrank (ZMod 2) (Coh (ZMod 2) X (4 - (2 + 2))) = 1 := by
          rw [show 4 - (2 + 2) = 0 from by norm_num]
          exact hX0
        have h2 : Module.finrank (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) (2 + 1)) = 1 := by
          rw [show 2 + 1 = 3 from by norm_num]
          exact hF3
        rw [h1, h2, if_pos rfl, mul_one]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [show Finset.range (4 - 1) = Finset.range 3 from rfl, Finset.sum_ite_eq',
      if_pos (Finset.mem_range.mpr (by norm_num))]
  have hb4ne : Module.finrank (ZMod 2) (Coh (ZMod 2) X 4) ≠ 0 := by
    intro hzero
    have hsub : Subsingleton (Coh (ZMod 2) X 4) := by
      haveI : FiniteDimensional (ZMod 2) (Coh (ZMod 2) X 4) := hBfin 4 (by omega)
      exact Module.finrank_zero_iff.mp hzero
    have hE2 : IsZero (S.E 2 ((4 : ℤ), (0 : ℤ))) :=
      k4_isZero_E2_left' (p := k4PathFib x₀) (e₀ := k4PathBase x₀) (N := 8) (S := S)
        (hS := hSS) (s := 4) (q := 0) (by norm_num) (by norm_num) hsub
    have hE4 : IsZero (S.E 4 ((4 : ℤ), (0 : ℤ))) := k4_isZero_E_of_isZero_E2 S hE2 (by norm_num)
    have h0 : (S.d 4 ((0 : ℤ), (3 : ℤ)) ((4 : ℤ), (0 : ℤ))).hom u = 0 := by
      have h1 : (S.d 4 ((0 : ℤ), (3 : ℤ)) ((4 : ℤ), (0 : ℤ))) = 0 := hE4.eq_of_tgt _ _
      rw [h1]
      simp
    exact hu (show (S.d 4 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 4)).hom u = 0 from h0)
  have hb4 : Module.finrank (ZMod 2) (Coh (ZMod 2) X 4) = 1 := by
    omega
  -- ## the crux
  have h8E : Module.finrank (ZMod 2) (S.E 8 ((0 : ℤ), (7 : ℤ))) ≤ 1 :=
    k4_crux (k4PathFib x₀) (k4PathBase x₀) 8 S hSS (by norm_num)
      (fun s hs => hBfin s (by omega)) (fun q hq => hFfin q hq)
      hX0 hF0 hb4 hF3 hF4 hF7 hB1 hB2 hB3 hF1 hF2 (hE 8 (by norm_num) (by omega))
      u (show (S.d 4 ((0 : ℤ), (3 : ℤ)) ((4 : ℤ), (0 : ℤ))).hom u ≠ 0 from hu) hco
  -- ## the two conclusions
  refine ⟨?_, ?_⟩
  · exact K4F.sevenBound (k4PathFib x₀) (k4PathBase x₀) 8 S hSS (by norm_num)
      (fun s hs => hBfin s (by omega)) (fun q hq => hFfin q hq)
      hX0 hF0 hB1 hB2 hB3 hF1 hF2 hF6 (hE 7 (by norm_num) (by omega))
  · exact K4F.eightBound (k4PathFib x₀) (k4PathBase x₀) 8 S hSS (by norm_num)
      (fun s hs => hBfin s (by omega)) (fun q hq => hFfin q hq)
      hF0 hb4 hF3 hB1 hB2 hB3 hF1 hF2 (hE 8 (by norm_num) (by omega)) h8E

end

end Work.Pi6.EMM2
