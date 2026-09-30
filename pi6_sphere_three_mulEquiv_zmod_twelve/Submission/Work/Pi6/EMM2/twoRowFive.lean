import Mathlib
import Submission.Work.Pi6.EMM2.Defs
import Submission.Work.Pi6.EMM2.SerreKit
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-!
# Area EMM2 — the two-row forcing argument in the stable range `N = 5`

`Work.Pi6.EMM2.twoRowFive` is the two-row consequence of a multiplicative Serre spectral sequence
(`Work.Pi6.CohSS`, `Work.Pi6.IsSerreMSS`) that the assembly of `π₆(S³) = ℤ/12` uses for the base of
the fibration `S¹ → S⁷ → ℂP³`: if a fibration `p : E → B` has a fibre whose cohomology is
`𝕜, 𝕜, 0, …` (a `K(ℤ,1)`-like fibre) and a total space that is `𝕜`-acyclic through degree `5`, and
the base has `H⁰ = 𝕜` and is of finite type, then through degree `5` the base looks like
`𝕜[w]`: there is a class `w ∈ H²(B)` with `w^k ≠ 0`, `dim H^{2k}(B) = 1` and `H^{2k+1}(B) = 0`.

The mathematical argument (two rows only, so `d₂` is the only differential in the strip):

* `E₂^{s,q} = H^s(B) ⊗ H^q(F)` vanishes for `q ≥ 2`; hence on the row `q = 1` the only differential
  is `d₂ : E₂^{s,1} → E₂^{s+2,0}`, and `E_{k+2}^{s,1} = ker d₂` for `k ≥ 0`, `E_{k+2}^{s,0} = coker d₂`.
* `H^n(E) = 0` (`1 ≤ n ≤ 5`) gives, from the convergence clause `Σ_s dim E_{n+2}^{s,n-s} = dim H^n(E)`,
  that `E_{n+2}^{n,0} = E_{n+2}^{n-1,1} = 0`.  In particular `E₅^{2,1} = 0`: a nonzero cycle in
  `E₂^{2,1}` would survive to `E₅^{2,1} ≠ 0` (nothing hits it, and its differentials land in
  negative rows), so `ker(d₂ : E₂^{2,1} → E₂^{4,0}) = 0`.
* The column edge (`hcol` of `IsSerreMSS`) shows that `u = e₂^{-1}(1 ⊗ f)`, `f ≠ 0 ∈ H¹(F)`, is *not*
  a cycle: `e := d₂u ≠ 0`.  Its `e₂`-image is `w ⊗ 1`, `w ∈ H²(B)`, `w ≠ 0`.
* Multiplicativity + Leibniz: `e₂^{-1}(w^k ⊗ 1)` is a cycle for every `k`, `d₂(mul(b,u)) = mul(b,e)`,
  and the total space's vanishing (`E_{2k+1}^{2k,1} = 0`) forces each of these cycles to survive: so
  `w^k ≠ 0` and `dim H^{2k}(B) = 1`; the telescoped row bound `dim H^n(B) ≤ dim H^{n-2}(B)`
  (`SerreKit.finrank_row0_bound`) gives the matching upper bounds.

The file below also contains, in the `tr5_`-prefixed form (copied from the colleague module
`Submission/Work/Pi6/EMM2/twoRowKit.lean` so that this module is self-contained), the general
two-row forcing lemma `tr5_twoRowGen`, whose hypothesis `8 ≤ N` is *not used* by its proof: this is
what makes the argument available at `N = 5`.

-/

namespace Work.Pi6.EMM2

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝕜 : Type} [Field 𝕜]

/-! ## Elementary helpers -/

/-- The unit of `H⁰` is nonzero when `H⁰` is one-dimensional. -/
theorem tr5_one_ne_zero {Y : Type} [TopologicalSpace Y]
    (h0 : Module.finrank 𝕜 (Coh 𝕜 Y 0) = 1) : one 𝕜 Y ≠ 0 := by
  intro hone
  have hsub : Subsingleton (Coh 𝕜 Y 0) := ⟨fun a b => by
    have ha : cup 𝕜 Y 0 0 (one 𝕜 Y) a = a := by
      show ((Work.Cohomology.cupH' 𝕜 (TopCat.toSSet.obj (TopCat.of Y)) 0 0)
        (Work.Cohomology.oneH 𝕜 (TopCat.toSSet.obj (TopCat.of Y)))) a = a
      exact Work.Cohomology.cupH'_one_left 𝕜 (TopCat.toSSet.obj (TopCat.of Y)) 0 a
    have hb : cup 𝕜 Y 0 0 (one 𝕜 Y) b = b := by
      show ((Work.Cohomology.cupH' 𝕜 (TopCat.toSSet.obj (TopCat.of Y)) 0 0)
        (Work.Cohomology.oneH 𝕜 (TopCat.toSSet.obj (TopCat.of Y)))) b = b
      exact Work.Cohomology.cupH'_one_left 𝕜 (TopCat.toSSet.obj (TopCat.of Y)) 0 b
    rw [← ha, ← hb, hone]
    simp⟩
  have hfd : FiniteDimensional 𝕜 (Coh 𝕜 Y 0) :=
    FiniteDimensional.of_finrank_pos (by rw [h0]; norm_num)
  rw [Module.finrank_zero_iff.mpr hsub] at h0
  omega

/-- A finite-dimensional module of dimension zero is a subsingleton. -/
theorem tr5_subsingleton_of_finrank_zero {M : Type} [AddCommGroup M] [Module 𝕜 M]
    [FiniteDimensional 𝕜 M] (h : Module.finrank 𝕜 M = 0) : Subsingleton M :=
  Module.finrank_zero_iff.mp h

/-- A module of dimension one has a nonzero element. -/
theorem tr5_exists_ne_zero {M : Type} [AddCommGroup M] [Module 𝕜 M]
    (h : Module.finrank 𝕜 M = 1) : ∃ x : M, x ≠ 0 := by
  by_contra hc
  push_neg at hc
  have hsub : Subsingleton M := ⟨fun a b => by rw [hc a, hc b]⟩
  have hfd : FiniteDimensional 𝕜 M := FiniteDimensional.of_finrank_pos (by rw [h]; norm_num)
  rw [Module.finrank_zero_iff.mpr hsub] at h
  omega

/-- Monotonicity of `IsEMSpaceUpTo` in the range. -/
theorem tr5_isEMSpaceUpTo_mono {A : Type} [AddCommGroup A] {m : ℕ} (hm : 0 < m) {M M' : ℕ}
    {X : Type} [TopologicalSpace X] {x : X} (h : Work.Serre.IsEMSpaceUpTo A m hm M X x)
    (hM : M' ≤ M) : Work.Serre.IsEMSpaceUpTo A m hm M' X x :=
  ⟨h.1, fun i hi hc => h.2 i hi (hc.imp id (fun hle => le_trans hle hM))⟩

/-- The dimension of a zero module is zero. -/
theorem tr5_finrank_eq_zero_of_isZero {M : Type} [AddCommGroup M] [Module 𝕜 M]
    (h : IsZero (ModuleCat.of 𝕜 M)) : Module.finrank 𝕜 M = 0 := by
  haveI : Subsingleton (ModuleCat.of 𝕜 M) := ModuleCat.subsingleton_of_isZero h
  exact Module.finrank_eq_zero_of_subsingleton 𝕜 M

/-- An isomorphism of modules applied to the inverse of a class. -/
theorem tr5_iso_hom_inv_hom_apply {M N : ModuleCat 𝕜} (e : M ≅ N) (y : N) :
    e.hom (e.inv.hom y) = y := by
  have h := e.toLinearEquiv.apply_symm_apply y
  simpa using h

/-- An isomorphism of modules followed by its inverse. -/
theorem tr5_iso_inv_hom_apply {M N : ModuleCat 𝕜} (e : M ≅ N) (x : M) :
    e.inv.hom (e.hom x) = x := by
  have h := e.toLinearEquiv.symm_apply_apply x
  simpa using h

/-- The dimension of a vanishing cohomology group is zero. -/
theorem tr5_finrank_eq_zero_of_isZero_cohom {Y : Type} [TopologicalSpace Y] {n : ℕ}
    (h : IsZero (Coh 𝕜 Y n)) : Module.finrank 𝕜 (Coh 𝕜 Y n) = 0 := by
  haveI : Subsingleton (Coh 𝕜 Y n) := ModuleCat.subsingleton_of_isZero h
  exact Module.finrank_eq_zero_of_subsingleton 𝕜 (Coh 𝕜 Y n)

/-- `IsZero` of a `𝕜`-module from `IsZero` of the underlying type. -/
theorem tr5_isZero_of_subsingleton {M : Type} [AddCommGroup M] [Module 𝕜 M]
    [Subsingleton M] : IsZero (ModuleCat.of 𝕜 M) :=
  ModuleCat.isZero_of_subsingleton _

/-! ## The two-row forcing argument -/

section TwoRow

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The row `q ≥ 2` of the spectral sequence vanishes at every page.** -/
theorem tr5_rowGone (p : C(E, B)) (e₀ : E) (N : ℕ) (S : CohSS 𝕜)
    (hS : IsSerreMSS S p e₀ N)
    (hFq : ∀ q : ℕ, 2 ≤ q → q ≤ N → IsZero (Coh 𝕜 (Fib p e₀) q))
    (s q : ℕ) (h2 : 2 ≤ q) (hq : q ≤ N) (hs : s ≤ N) :
    ∀ r : ℕ, 2 ≤ r → IsZero (S.E r ((s : ℤ), (q : ℤ))) := by
  obtain ⟨e2, _⟩ := hS
  haveI hsub : Subsingleton (Coh 𝕜 (Fib p e₀) q) :=
    ModuleCat.subsingleton_of_isZero (hFq q h2 hq)
  haveI hten : Subsingleton (TensorProduct 𝕜 (Coh 𝕜 B s) (Coh 𝕜 (Fib p e₀) q)) :=
    inferInstance
  have h2e : IsZero (S.E 2 ((s : ℤ), (q : ℤ))) :=
    IsZero.of_iso (ModuleCat.isZero_of_subsingleton (ModuleCat.of 𝕜
      (TensorProduct 𝕜 (Coh 𝕜 B s) (Coh 𝕜 (Fib p e₀) q)))) (e2 s q hs hq)
  intro r hr
  have := CohSS.isZero_two_of S ((s : ℤ), (q : ℤ)) h2e (r - 2)
  rwa [show r - 2 + 2 = r from by omega] at this

/-- **A nonzero cycle that nothing hits survives to a given later page.**  Restricted form of
`CohSS.not_isZero_of_survives` with the vanishing hypotheses only up to the page reached. -/
theorem tr5_survives (S : CohSS 𝕜) (a : ℤ × ℤ) (t : ℕ) (x : S.E 2 a)
    (hcyc : (S.d 2 a (a + vr 2)).hom x = 0) (hx0 : x ≠ 0)
    (hsrc : ∀ j : ℕ, 2 ≤ j → j ≤ 2 + t → IsZero (S.E j (a - vr j)))
    (htgt : ∀ j : ℕ, 3 ≤ j → j ≤ 2 + t → IsZero (S.E j (a + vr j))) :
    ∃ y : S.E (2 + t) a, y ≠ 0 := by
  have key : ∀ s : ℕ, s ≤ t → ∃ y : S.E (2 + s) a,
      y ≠ 0 ∧ (S.d (2 + s) a (a + vr (2 + s))).hom y = 0 := by
    intro s _
    induction s with
    | zero => exact ⟨x, hx0, hcyc⟩
    | succ s ih =>
        obtain ⟨y, hy, hyc⟩ := ih (by omega)
        have h2s : 2 ≤ 2 + s := by omega
        have hznext : IsZero (S.E (2 + (s + 1)) (a + vr (2 + (s + 1)))) :=
          htgt (2 + (s + 1)) (by omega) (by omega)
        refine ⟨S.proj (2 + s) a ⟨y, hyc⟩, ?_, ?_⟩
        · intro hy'
          have hmem : y ∈ LinearMap.range (S.d (2 + s) (a - vr (2 + s)) a).hom :=
            (S.proj_ker (2 + s) a h2s ⟨y, hyc⟩).mp hy'
          obtain ⟨z, hz⟩ := hmem
          haveI : Subsingleton (S.E (2 + s) (a - vr (2 + s))) :=
            ModuleCat.subsingleton_of_isZero (hsrc (2 + s) (by omega) (by omega))
          rw [Subsingleton.elim z 0, map_zero] at hz
          exact hy hz.symm
        · rw [S.d_eq_zero_of_isZero (r := 2 + (s + 1)) (a := a)
            (b := a + vr (2 + (s + 1))) hznext]
          simp
  obtain ⟨y, hy, -⟩ := key t le_rfl
  exact ⟨y, hy⟩


/-- **The dimension bound along the row `q = 0`, at `n = 1`.** -/
theorem tr5_finrank_one_eq_zero (p : C(E, B)) (e₀ : E) (N : ℕ) (S : CohSS 𝕜)
    (hS : IsSerreMSS S p e₀ N)
    (hB : ∀ s : ℕ, s ≤ N → FiniteDimensional 𝕜 (Coh 𝕜 B s))
    (hF : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜 (Coh 𝕜 (Fib p e₀) q))
    (hF0 : Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) 0) = 1)
    (hE : ∀ n : ℕ, 1 ≤ n → n ≤ N → IsZero (Coh 𝕜 E n)) (hN : 1 ≤ N) :
    Module.finrank 𝕜 (Coh 𝕜 B 1) = 0 := by
  have hb := finrank_row0_bound S p e₀ N hS hB hF hF0 1 hN
  have hE1 : Module.finrank 𝕜 (Coh 𝕜 E 1) = 0 :=
    tr5_finrank_eq_zero_of_isZero_cohom (hE 1 le_rfl hN)
  rw [hE1, zero_add] at hb
  have hz : (∑ r ∈ Finset.range (1 - 1), Module.finrank 𝕜 (Coh 𝕜 B (1 - (r + 2))) *
      Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) (r + 1))) = 0 := by simp
  rw [hz] at hb
  omega

/-- **The dimension bound along the row `q = 0`.**  `dim H^n(B) ≤ dim H^{n-2}(B)` for `2 ≤ n ≤ N`. -/
theorem tr5_finrank_le_sub_two (p : C(E, B)) (e₀ : E) (N : ℕ) (S : CohSS 𝕜)
    (hS : IsSerreMSS S p e₀ N)
    (hB : ∀ s : ℕ, s ≤ N → FiniteDimensional 𝕜 (Coh 𝕜 B s))
    (hF : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜 (Coh 𝕜 (Fib p e₀) q))
    (hF0 : Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) 0) = 1)
    (hF1 : Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) 1) = 1)
    (hFq : ∀ q : ℕ, 2 ≤ q → q ≤ N → IsZero (Coh 𝕜 (Fib p e₀) q))
    (hE : ∀ n : ℕ, 1 ≤ n → n ≤ N → IsZero (Coh 𝕜 E n))
    (n : ℕ) (hn : 2 ≤ n) (hnN : n ≤ N) :
    Module.finrank 𝕜 (Coh 𝕜 B n) ≤ Module.finrank 𝕜 (Coh 𝕜 B (n - 2)) := by
  have hb := finrank_row0_bound S p e₀ N hS hB hF hF0 n hnN
  have hEn : Module.finrank 𝕜 (Coh 𝕜 E n) = 0 :=
    tr5_finrank_eq_zero_of_isZero_cohom (hE n (by omega) hnN)
  rw [hEn, zero_add] at hb
  refine hb.trans ?_
  have hterm : ∀ r ∈ Finset.range (n - 1),
      Module.finrank 𝕜 (Coh 𝕜 B (n - (r + 2))) * Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) (r + 1))
        ≤ if r = 0 then Module.finrank 𝕜 (Coh 𝕜 B (n - 2)) else 0 := by
    intro r hr
    rw [Finset.mem_range] at hr
    by_cases h : r = 0
    · subst h
      simp only [ite_true, Nat.reduceAdd]
      rw [hF1, mul_one]
    · simp only [h, ite_false]
      have hz : Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) (r + 1)) = 0 :=
        tr5_finrank_eq_zero_of_isZero_cohom (hFq (r + 1) (by omega) (by omega))
      rw [hz, mul_zero]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]


/-- **The two-row forcing argument.**  For a Serre fibration `p : E → B` whose spectral sequence over
`𝕜` is available in range `N ≥ 8`, whose base has `H⁰ = 𝕜` and finite type through `N`, whose fibre
has cohomology `𝕜, 𝕜, 0, …` through `N` and whose total space is `𝕜`-acyclic above degree `0`: there
is `w ∈ H²(B;𝕜)` with `w^k ≠ 0`, `dim H^{2k}(B;𝕜) = 1` (for `2k ≤ N`) and `H^{2k+1}(B;𝕜) = 0`
(for `2k+1 ≤ N`). -/
theorem tr5_twoRowGen (p : C(E, B)) (e₀ : E) (N : ℕ) (S : CohSS 𝕜)
    (hS : IsSerreMSS S p e₀ N) (hN : 2 ≤ N)
    (hB0 : Module.finrank 𝕜 (Coh 𝕜 B 0) = 1)
    (hBfin : ∀ s : ℕ, s ≤ N → FiniteDimensional 𝕜 (Coh 𝕜 B s))
    (hF0 : Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) 0) = 1)
    (hF1 : Module.finrank 𝕜 (Coh 𝕜 (Fib p e₀) 1) = 1)
    (hFq : ∀ q : ℕ, 2 ≤ q → q ≤ N → IsZero (Coh 𝕜 (Fib p e₀) q))
    (hE : ∀ n : ℕ, 1 ≤ n → n ≤ N → IsZero (Coh 𝕜 E n)) :
    ∃ w : Coh 𝕜 B 2,
      (∀ k : ℕ, 2 * k ≤ N → cpow w k ≠ 0) ∧
      (∀ k : ℕ, 2 * k ≤ N → Module.finrank 𝕜 (Coh 𝕜 B (2 * k)) = 1) ∧
      (∀ k : ℕ, 2 * k + 1 ≤ N → Subsingleton (Coh 𝕜 B (2 * k + 1))) := by
  have hSS : IsSerreMSS S p e₀ N := hS
  obtain ⟨e2, hmul, hconv0, hconv, hbot, hcol⟩ := hS
  -- finiteness of the fibre's cohomology in the range
  have hFfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜 (Coh 𝕜 (Fib p e₀) q) := by
    intro q hq
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      exact FiniteDimensional.of_finrank_pos (by rw [hF0]; norm_num)
    · rcases eq_or_lt_of_le (show 1 ≤ q by omega) with h1 | h1
      · subst h1
        exact FiniteDimensional.of_finrank_pos (by rw [hF1]; norm_num)
      · haveI : Subsingleton (Coh 𝕜 (Fib p e₀) q) :=
          ModuleCat.subsingleton_of_isZero (hFq q (by omega) hq)
        infer_instance
  -- finiteness of the pages from page 2
  have hpage : ∀ (r : ℕ) (a : ℤ × ℤ), FiniteDimensional 𝕜 (S.E 2 a) →
      FiniteDimensional 𝕜 (S.E (r + 2) a) := by
    intro r
    induction r with
    | zero => intro a h; simpa using h
    | succ r ih =>
        intro a h2
        haveI := ih a h2
        exact FiniteDimensional.of_surjective (S.proj (r + 2) a) (S.proj_surj (r + 2) a (by omega))
  -- a nonzero class in the fibre's `H¹`
  obtain ⟨f, hf⟩ := tr5_exists_ne_zero (𝕜 := 𝕜) hF1
  -- the classes `u ∈ E₂^{0,1}` and `e = d₂ u`
  let u : S.E 2 ((0 : ℤ), (1 : ℤ)) :=
    (e2 0 1 (by norm_num) (by omega)).inv.hom (one 𝕜 B ⊗ₜ[𝕜] f)
  let e0 : S.E 2 (((0 : ℤ), (1 : ℤ)) + vr 2) :=
    (S.d 2 ((0 : ℤ), (1 : ℤ)) (((0 : ℤ), (1 : ℤ)) + vr 2)).hom u
  -- `e ≠ 0`, from the column edge
  have he0 : e0 ≠ 0 := by
    intro he0zero
    have hLHS : ¬ ∃ e' : Coh 𝕜 E 1,
        (cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) 1).hom e' = f := by
      rintro ⟨e', he'⟩
      haveI : Subsingleton (Coh 𝕜 E 1) :=
        ModuleCat.subsingleton_of_isZero (hE 1 (by norm_num) (by omega))
      rw [Subsingleton.elim e' 0, map_zero] at he'
      exact hf he'.symm
    have hRHS := (hcol 1 (by omega) f).mpr
    apply hLHS
    apply hRHS
    refine ⟨S.proj 2 ((0 : ℤ), (1 : ℤ)) ⟨u, he0zero⟩, ?_⟩
    show ((S.colTo (1 : ℤ) 1).hom (S.proj 2 ((0 : ℤ), (1 : ℤ)) ⟨u, he0zero⟩)) = u
    simp only [CohSS.colTo, Category.comp_id, ModuleCat.hom_comp, ModuleCat.hom_id]
    exact S.col_spec 2 1 ⟨u, he0zero⟩ (by norm_num)
  -- the class `w ∈ H²(B;𝕜)` carried by `e`
  have honeF : one 𝕜 (Fib p e₀) ≠ 0 := tr5_one_ne_zero hF0
  have hspan : Submodule.span 𝕜 ({one 𝕜 (Fib p e₀)} : Set (Coh 𝕜 (Fib p e₀) 0)) = ⊤ := by
    haveI : FiniteDimensional 𝕜 (Coh 𝕜 (Fib p e₀) 0) :=
      FiniteDimensional.of_finrank_pos (by rw [hF0]; norm_num)
    exact Submodule.eq_top_of_finrank_eq (by rw [finrank_span_singleton honeF, hF0])
  have hdecomp : ∀ y : TensorProduct 𝕜 (Coh 𝕜 B 2) (Coh 𝕜 (Fib p e₀) 0),
      ∃ w : Coh 𝕜 B 2, y = w ⊗ₜ[𝕜] one 𝕜 (Fib p e₀) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a c =>
        obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp
          (show c ∈ Submodule.span 𝕜 ({one 𝕜 (Fib p e₀)} : Set _) by rw [hspan]; trivial)
        have hlamk : (lam : 𝕜) • one 𝕜 (Fib p e₀) = c := hlam
        refine ⟨lam • a, ?_⟩
        rw [← hlamk]
        exact (TensorProduct.tmul_smul lam a (one 𝕜 (Fib p e₀))).trans
          (TensorProduct.smul_tmul' lam a (one 𝕜 (Fib p e₀)))
    | add y z hy hz =>
        obtain ⟨wy, hwy⟩ := hy
        obtain ⟨wz, hwz⟩ := hz
        exact ⟨wy + wz, by rw [hwy, hwz, TensorProduct.add_tmul]⟩
  obtain ⟨w, hw⟩ := hdecomp ((e2 2 0 (by omega) (by norm_num)).hom e0)
  have he0' : (e2 2 0 (by omega) (by norm_num)).inv.hom
      (w ⊗ₜ[𝕜] one 𝕜 (Fib p e₀)) = e0 := by
    rw [← hw]
    exact tr5_iso_inv_hom_apply (e2 2 0 (by omega) (by norm_num)) e0
  have hpow : ∀ k : ℕ, 2 * k ≤ N → cpow w k ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; exact tr5_one_ne_zero hB0
    | succ k ih =>
        intro hk
        have hkN : 2 * k ≤ N := by omega
        have hkw : cpow w k ≠ 0 := ih hkN
        let bk : S.E 2 (((2 * k : ℕ) : ℤ), ((0 : ℕ) : ℤ)) :=
          (e2 (2 * k) 0 (by omega) (by norm_num)).inv.hom
            (cpow w k ⊗ₜ[𝕜] one 𝕜 (Fib p e₀))
        let ck : S.E 2 (((2 * k + 0 : ℕ) : ℤ), ((0 + 1 : ℕ) : ℤ)) :=
          S.mul 2 (((2 * k : ℕ) : ℤ), ((0 : ℕ) : ℤ)) (((0 : ℕ) : ℤ), ((1 : ℕ) : ℤ))
            (((2 * k + 0 : ℕ) : ℤ), ((0 + 1 : ℕ) : ℤ)) (by ext <;> simp) bk u
        have hDB : (((2 * k : ℕ) : ℤ), ((0 : ℕ) : ℤ))
            + (((0 : ℕ) : ℤ), ((1 : ℕ) : ℤ))
            = (((2 * k + 0 : ℕ) : ℤ), ((0 + 1 : ℕ) : ℤ)) := by ext <;> simp
        have hdbk : (S.d 2 (((2 * k : ℕ) : ℤ), ((0 : ℕ) : ℤ))
            ((((2 * k : ℕ) : ℤ), ((0 : ℕ) : ℤ)) + vr 2)).hom bk = 0 := by
          have hneg : (((((2 * k : ℕ) : ℤ), ((0 : ℕ) : ℤ))) + vr 2).2 < 0 := by
            simp only [Work.Pi6.vr, Prod.snd_add, Prod.snd_ofNat]
            omega
          rw [S.d_eq_zero_of_isZero (r := 2)
            (a := (((2 * k : ℕ) : ℤ), ((0 : ℕ) : ℤ)))
            (b := ((((2 * k : ℕ) : ℤ), ((0 : ℕ) : ℤ)) + vr 2))
            (CohSS.isZero_quad S 2 _ (Or.inr hneg))]
          simp
        have hleib := S.leibniz 2 (((2 * k : ℕ) : ℤ), ((0 : ℕ) : ℤ))
          (((0 : ℕ) : ℤ), ((1 : ℕ) : ℤ)) (((2 * k + 0 : ℕ) : ℤ), ((0 + 1 : ℕ) : ℤ))
          hDB bk u (by norm_num)
        have hdck : (S.d 2 (((2 * k + 0 : ℕ) : ℤ), ((0 + 1 : ℕ) : ℤ))
              ((((2 * k + 0 : ℕ) : ℤ), ((0 + 1 : ℕ) : ℤ)) + vr 2)).hom ck
            = (e2 (2 * k + 2) 0 (by omega) (by norm_num)).inv.hom
                (cpow w (k + 1) ⊗ₜ[𝕜] one 𝕜 (Fib p e₀)) := by
          rw [hleib, hdbk]
          simp only [LinearMap.zero_apply, LinearMap.map_zero, zero_add]
          have hperm : (((2 * k : ℕ) : ℤ), ((0 : ℕ) : ℤ)) + (((2 : ℕ) : ℤ), ((0 : ℕ) : ℤ))
              = (((2 * k + 2 : ℕ) : ℤ), ((0 + 0 : ℕ) : ℤ)) := by ext <;> simp
          change ((-1 : 𝕜) ^ (2 * k)) •
              S.mul 2 (((2 * k : ℕ) : ℤ), ((0 : ℕ) : ℤ)) (((2 : ℕ) : ℤ), ((0 : ℕ) : ℤ))
                (((2 * k + 2 : ℕ) : ℤ), ((0 + 0 : ℕ) : ℤ)) hperm bk
                ((S.d 2 (((0 : ℕ) : ℤ), ((1 : ℕ) : ℤ))
                  ((((0 : ℕ) : ℤ), ((1 : ℕ) : ℤ)) + vr 2)).hom u)
            = (e2 (2 * k + 2) 0 (by omega) (by norm_num)).inv.hom
                (cpow w (k + 1) ⊗ₜ[𝕜] one 𝕜 (Fib p e₀))
          rw [pow_mul, neg_one_sq, one_pow, one_smul]
          rw [show (S.d 2 (((0 : ℕ) : ℤ), ((1 : ℕ) : ℤ))
              ((((0 : ℕ) : ℤ), ((1 : ℕ) : ℤ)) + vr 2)).hom u = e0 from rfl]
          rw [← he0']
          have hm := hmul (2 * k) 0 2 0 (cpow w k) (one 𝕜 (Fib p e₀)) w
            (one 𝕜 (Fib p e₀)) (by omega) (by omega)
          refine hm.trans ?_
          rw [show ((0 : ℕ) * 2) = 0 from rfl, pow_zero, one_smul]
          rw [show (cup 𝕜 B (2 * k) 2) (cpow w k) w = cpow w (k + 1) from rfl]
          rw [show (cup 𝕜 (Fib p e₀) 0 0) (one 𝕜 (Fib p e₀)) (one 𝕜 (Fib p e₀))
              = one 𝕜 (Fib p e₀) from
            Work.Cohomology.cupH'_one_right 𝕜 (TopCat.toSSet.obj (TopCat.of (Fib p e₀))) 0
              (Work.Cohomology.oneH 𝕜 (TopCat.toSSet.obj (TopCat.of (Fib p e₀))))]
        have hck_ne : ck ≠ 0 := by
          have hm2 := hmul (2 * k) 0 0 1 (cpow w k) (one 𝕜 (Fib p e₀)) (one 𝕜 B) f
            (by omega) (by omega)
          have h1 : (cup 𝕜 B (2 * k) 0) (cpow w k) (one 𝕜 B) = cpow w k := by
            show ((Work.Cohomology.cupH' 𝕜 (TopCat.toSSet.obj (TopCat.of B)) (2 * k) 0)
              (cpow w k)) (Work.Cohomology.oneH 𝕜 (TopCat.toSSet.obj (TopCat.of B))) = _
            exact Work.Cohomology.cupH'_one_right 𝕜 (TopCat.toSSet.obj (TopCat.of B))
              (2 * k) (cpow w k)
          have h2 : (cup 𝕜 (Fib p e₀) 0 1) (one 𝕜 (Fib p e₀)) f = f := by
            show ((Work.Cohomology.cupH' 𝕜 (TopCat.toSSet.obj (TopCat.of (Fib p e₀))) 0 1)
              (Work.Cohomology.oneH 𝕜 (TopCat.toSSet.obj (TopCat.of (Fib p e₀))))) f = f
            rw [Work.Cohomology.cupH'_one_left 𝕜
              (TopCat.toSSet.obj (TopCat.of (Fib p e₀))) 1 f]
          have hck_eq : ck = (e2 (2 * k) 1 (by omega) (by omega)).inv.hom
              (cpow w k ⊗ₜ[𝕜] f) := by
            refine hm2.trans ?_
            rw [show ((0 : ℕ) * 0) = 0 from rfl, pow_zero, one_smul, h1, h2]
            rfl
          rw [hck_eq]
          intro h0
          have hten : cpow w k ⊗ₜ[𝕜] f ≠ 0 := tmul_ne_zero_of_ne_zero hkw hf
          have hkey := congrArg (fun z => (e2 (2 * k) 1 (by omega) (by omega)).hom z) h0
          rw [map_zero, tr5_iso_hom_inv_hom_apply] at hkey
          exact hten hkey
        have hdk_ne : (S.d 2 (((2 * k + 0 : ℕ) : ℤ), ((0 + 1 : ℕ) : ℤ))
            ((((2 * k + 0 : ℕ) : ℤ), ((0 + 1 : ℕ) : ℤ)) + vr 2)).hom ck ≠ 0 := by
          intro hd0
          have hzero : IsZero (S.E ((2 * k + 1) + 2)
              ((((2 * k : ℕ) : ℤ), ((1 : ℕ) : ℤ)))) := by
            have hsum := hconv (2 * k + 1) (by omega)
            have hEn : Module.finrank 𝕜 (Coh 𝕜 E (2 * k + 1)) = 0 :=
              tr5_finrank_eq_zero_of_isZero_cohom (hE (2 * k + 1) (by omega) (by omega))
            rw [hEn] at hsum
            have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp hsum
            have hk' := hterm (2 * k) (Finset.mem_range.mpr (by omega))
            have hidx : (2 * k + 1) - 2 * k = 1 := by omega
            rw [hidx] at hk'
            haveI : FiniteDimensional 𝕜
                (S.E ((2 * k + 1) + 2) ((((2 * k : ℕ) : ℤ), ((1 : ℕ) : ℤ)))) := by
              haveI : FiniteDimensional 𝕜 (S.E 2 ((((2 * k : ℕ) : ℤ), ((1 : ℕ) : ℤ)))) := by
                haveI : FiniteDimensional 𝕜 (Coh 𝕜 B (2 * k)) := hBfin (2 * k) (by omega)
                haveI : FiniteDimensional 𝕜 (Coh 𝕜 (Fib p e₀) 1) := hFfin 1 (by omega)
                exact (e2 (2 * k) 1 (by omega) (by omega)).toLinearEquiv.symm.finiteDimensional
              simpa using hpage (2 * k + 1) ((((2 * k : ℕ) : ℤ), ((1 : ℕ) : ℤ))) this
            haveI : Subsingleton
                (S.E ((2 * k + 1) + 2) ((((2 * k : ℕ) : ℤ), ((1 : ℕ) : ℤ)))) :=
              Module.finrank_zero_iff.mp hk'
            exact ModuleCat.isZero_of_subsingleton _
          have hsrc : ∀ j : ℕ, 2 ≤ j → j ≤ 2 + (2 * k + 1) →
              IsZero (S.E j ((((2 * k : ℕ) : ℤ), ((1 : ℕ) : ℤ)) - vr j)) := by
            intro j hj2 hj
            by_cases hjk : j ≤ 2 * k
            · have hbideg : ((((2 * k : ℕ) : ℤ), ((1 : ℕ) : ℤ)) - vr j)
                  = (((2 * k - j : ℕ) : ℤ), ((j : ℕ) : ℤ)) := by
                have h1 : (((2 * k : ℕ) : ℤ) - (j : ℤ)) = (((2 * k - j : ℕ)) : ℤ) :=
                  (Nat.cast_sub hjk).symm
                have h2 : ((1 : ℤ) - (1 - (j : ℤ))) = ((j : ℕ) : ℤ) := by
                  push_cast
                  ring
                rw [Work.Pi6.vr]
                refine Prod.ext ?_ ?_
                · simp only [Prod.fst_sub, Prod.fst_ofNat, Prod.snd_ofNat]
                  exact h1
                · simp only [Prod.snd_sub, Prod.snd_ofNat]
                  exact h2
              rw [hbideg]
              exact tr5_rowGone p e₀ N S hSS hFq (2 * k - j) j (by omega) (by omega)
                (by omega) j (by omega)
            · have hneg : ((((2 * k : ℕ) : ℤ), ((1 : ℕ) : ℤ)) - vr j).1 < 0 := by
                simp only [Work.Pi6.vr, Prod.fst_sub, Prod.fst_ofNat, Prod.snd_ofNat]
                omega
              exact CohSS.isZero_quad S j _ (Or.inl hneg)
          have htgt : ∀ j : ℕ, 3 ≤ j → j ≤ 2 + (2 * k + 1) →
              IsZero (S.E j ((((2 * k : ℕ) : ℤ), ((1 : ℕ) : ℤ)) + vr j)) := by
            intro j hj3 hj
            have hneg : ((((2 * k : ℕ) : ℤ), ((1 : ℕ) : ℤ)) + vr j).2 < 0 := by
              simp only [Work.Pi6.vr, Prod.snd_add, Prod.snd_ofNat]
              omega
            exact CohSS.isZero_quad S j _ (Or.inr hneg)
          have hsurv := tr5_survives S ((((2 * k : ℕ) : ℤ), ((1 : ℕ) : ℤ))) (2 * k + 1) ck
            hd0 hck_ne hsrc htgt
          obtain ⟨y, hy⟩ := hsurv
          haveI : Subsingleton (S.E (2 + (2 * k + 1)) ((((2 * k : ℕ) : ℤ), ((1 : ℕ) : ℤ)))) :=
            ModuleCat.subsingleton_of_isZero (by
              rw [show 2 + (2 * k + 1) = (2 * k + 1) + 2 from by omega]
              exact hzero)
          exact hy (Subsingleton.elim y 0)
        intro hw0
        have hfin : (e2 (2 * k + 2) 0 (by omega) (by norm_num)).inv.hom
            (cpow w (k + 1) ⊗ₜ[𝕜] one 𝕜 (Fib p e₀)) = 0 := by
          rw [hw0, TensorProduct.zero_tmul, map_zero]
        exact hdk_ne (hdck.trans hfin)
  refine ⟨w, hpow, ?_, ?_⟩
  · intro k hk
    have hle : Module.finrank 𝕜 (Coh 𝕜 B (2 * k)) ≤ 1 := by
      induction k with
      | zero => simpa using le_of_eq hB0
      | succ k ih =>
          have hstep := tr5_finrank_le_sub_two p e₀ N S hSS hBfin hFfin hF0 hF1 hFq hE
            (2 * (k + 1)) (by omega) (by omega)
          have heq : 2 * (k + 1) - 2 = 2 * k := by omega
          rw [heq] at hstep
          exact hstep.trans (ih (by omega))
    refine le_antisymm hle ?_
    haveI : FiniteDimensional 𝕜 (Coh 𝕜 B (2 * k)) := hBfin (2 * k) hk
    haveI : Nontrivial (Coh 𝕜 B (2 * k)) := ⟨cpow w k, 0, fun h => hpow k hk h⟩
    exact Module.finrank_pos
  · intro k hk
    have hz : Module.finrank 𝕜 (Coh 𝕜 B (2 * k + 1)) = 0 := by
      induction k with
      | zero => simpa using tr5_finrank_one_eq_zero p e₀ N S hSS hBfin hFfin hF0 hE (by omega)
      | succ k ih =>
          have hstep := tr5_finrank_le_sub_two p e₀ N S hSS hBfin hFfin hF0 hF1 hFq hE
            (2 * (k + 1) + 1) (by omega) (by omega)
          have heq : 2 * (k + 1) + 1 - 2 = 2 * k + 1 := by omega
          rw [heq] at hstep
          exact le_antisymm (hstep.trans (le_of_eq (ih (by omega)))) (Nat.zero_le _)
    haveI : FiniteDimensional 𝕜 (Coh 𝕜 B (2 * k + 1)) := hBfin (2 * k + 1) hk
    exact tr5_subsingleton_of_finrank_zero hz

end TwoRow


/-! ## The requested lemma -/

/-- **Area EMM2, `N = 5`.**  Two-row forcing in the range `5`: the base of a fibration with a
`K(ℤ,1)`-like fibre and `𝕜`-acyclic total space has the cohomology of `𝕜[w]`, `deg w = 2`, through
degree `5`. -/
theorem twoRowFive {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B) (e₀ : E) (S : Work.Pi6.CohSS 𝕜)
    (hS : Work.Pi6.IsSerreMSS S p e₀ 5)
    (hB0 : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 B 0) = 1)
    (hBfin : ∀ s : ℕ, s ≤ 5 → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 B s))
    (hF0 : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 0) = 1)
    (hF1 : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 1) = 1)
    (hFq : ∀ q : ℕ, 2 ≤ q → q ≤ 5 →
      CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (hE : ∀ n : ℕ, 1 ≤ n → n ≤ 5 → CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 E n)) :
    ∃ w : Work.Pi6.Coh 𝕜 B 2,
      w ≠ 0 ∧
      (∀ k : ℕ, 2 * k ≤ 5 → Work.Pi6.cpow w k ≠ 0) ∧
      (∀ k : ℕ, 2 * k ≤ 5 → Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 B (2 * k)) = 1) ∧
      (∀ k : ℕ, 2 * k + 1 ≤ 5 → Subsingleton (Work.Pi6.Coh 𝕜 B (2 * k + 1))) := by
  obtain ⟨w, hpow, hfin, hodd⟩ := tr5_twoRowGen p e₀ 5 S hS (by norm_num) hB0 hBfin hF0 hF1 hFq hE
  refine ⟨w, ?_, hpow, hfin, hodd⟩
  -- `w ≠ 0` is the case `k = 1` of the non-vanishing of the cup powers, since `cpow w 1` is the
  -- linear image of `w` (degree `0` factor the unit `cpow w 0`)
  intro hw0
  refine hpow 1 (by norm_num) ?_
  show (Work.Pi6.cup 𝕜 B (2 * 0) 2 (Work.Pi6.cpow w 0)) w = 0
  rw [hw0, map_zero]

end

end Work.Pi6.EMM2
