import Mathlib
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# A toolkit for the `CohSS` pages (area EMM2)

Basic structural lemmas about the abstract cohomological Serre spectral sequence `Work.Pi6.CohSS`:
vanishing in negative bidegrees, propagation of vanishing to higher pages, finiteness of the pages
(inherited from page `2`), monotonicity of dimensions along the pages, the per-step dimension
inequality, the telescoped dimension bound for the row `q = 0`, the "survival" lemma (a nonzero
cycle that nothing hits is nonzero on every later page), and the nonvanishing of a pure tensor.
-/

namespace Work.Pi6

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CohSS

variable {𝕜 : Type} [Field 𝕜]

/-- The source bidegree `(n,0) - vr r` of the `r`-th differential landing in the row `q = 0`. -/
def sr (n r : ℕ) : ℤ × ℤ := ((n : ℤ) - (r : ℤ), (r : ℤ) - 1)

theorem src_row0_eq (n r : ℕ) : (((n : ℤ), (0 : ℤ)) - vr r) = sr n r := by
  ext <;> simp [sr, vr]

/-- The pages vanish in negative bidegree. -/
theorem isZero_quad (S : CohSS 𝕜) (r : ℕ) (a : ℤ × ℤ) (h : a.1 < 0 ∨ a.2 < 0) :
    IsZero (S.E r a) :=
  S.quad r a h

/-- Vanishing propagates to the next page: `E_{r+1}` is a quotient of a submodule of `E_r`. -/
theorem isZero_succ (S : CohSS 𝕜) {r : ℕ} (hr : 2 ≤ r) (a : ℤ × ℤ) (h : IsZero (S.E r a)) :
    IsZero (S.E (r + 1) a) := by
  haveI hsub : Subsingleton (S.E r a) := ModuleCat.subsingleton_of_isZero h
  haveI : Subsingleton (S.E (r + 1) a) := ⟨fun x y => by
    obtain ⟨x', hx'⟩ := S.proj_surj r a hr x
    obtain ⟨y', hy'⟩ := S.proj_surj r a hr y
    rw [← hx', ← hy']
    exact congrArg (⇑(S.proj r a)) (Subtype.ext (Subsingleton.elim _ _))⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- A morphism into a vanishing module is zero. -/
theorem d_eq_zero_of_isZero (S : CohSS 𝕜) {r : ℕ} {a b : ℤ × ℤ} (h : IsZero (S.E r b)) :
    S.d r a b = 0 :=
  h.eq_of_tgt _ _

/-- Vanishing at page `2` propagates to every page. -/
theorem isZero_two_of (S : CohSS 𝕜) (a : ℤ × ℤ) (h : IsZero (S.E 2 a)) :
    ∀ k : ℕ, IsZero (S.E (k + 2) a) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have h2 := S.isZero_succ (r := k + 2) (by omega) a ih
      simpa [Nat.add_assoc] using h2

/-- A module in a negative bidegree is finite-dimensional (it is a zero object). -/
theorem finiteDimensional_of_neg (S : CohSS 𝕜) {r : ℕ} {a : ℤ × ℤ} (h : a.1 < 0 ∨ a.2 < 0) :
    FiniteDimensional 𝕜 (S.E r a) := by
  haveI : Subsingleton (S.E r a) := ModuleCat.subsingleton_of_isZero (S.quad r a h)
  exact FiniteDimensional.of_surjective (0 : 𝕜 →ₗ[𝕜] (S.E r a))
    (fun y => ⟨0, Subsingleton.elim _ _⟩)

/-- A module in a negative bidegree has dimension zero. -/
theorem finrank_eq_zero_of_neg (S : CohSS 𝕜) {r : ℕ} {a : ℤ × ℤ} (h : a.1 < 0 ∨ a.2 < 0) :
    Module.finrank 𝕜 (S.E r a) = 0 := by
  haveI : Subsingleton (S.E r a) := ModuleCat.subsingleton_of_isZero (S.quad r a h)
  exact Module.finrank_zero_of_subsingleton

/-- Finiteness of the pages in a box, inherited from page `2`. -/
theorem finiteDimensional_E (S : CohSS 𝕜) (N : ℕ)
    (hbox : ∀ a : ℤ × ℤ, 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ (N : ℤ) →
      FiniteDimensional 𝕜 (S.E 2 a)) :
    ∀ (k : ℕ) (a : ℤ × ℤ), 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ (N : ℤ) →
      FiniteDimensional 𝕜 (S.E (k + 2) a) := by
  intro k
  induction k with
  | zero => intro a h1 h2 h3; exact hbox a h1 h2 h3
  | succ k ih =>
      intro a h1 h2 h3
      haveI := ih a h1 h2 h3
      exact FiniteDimensional.of_surjective (S.proj (k + 2) a) (S.proj_surj (k + 2) a (by omega))

/-- The dimension does not increase along the pages. -/
theorem finrank_succ_le (S : CohSS 𝕜) {r : ℕ} (hr : 2 ≤ r) (a : ℤ × ℤ)
    (hfin : FiniteDimensional 𝕜 (S.E r a)) :
    Module.finrank 𝕜 (S.E (r + 1) a) ≤ Module.finrank 𝕜 (S.E r a) := by
  haveI := hfin
  have hP := LinearMap.finrank_range_add_finrank_ker (S.proj r a)
  have htop : LinearMap.range (S.proj r a) = ⊤ := LinearMap.range_eq_top.mpr (S.proj_surj r a hr)
  have hfr : Module.finrank 𝕜 ↥(LinearMap.range (S.proj r a)) =
      Module.finrank 𝕜 (S.E (r + 1) a) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ htop ≪≫ₗ Submodule.topEquiv)
  have hK : Module.finrank 𝕜 ↥(LinearMap.ker (S.d r a (a + vr r)).hom)
      ≤ Module.finrank 𝕜 (S.E r a) := Submodule.finrank_le _
  omega

/-- **The per-step dimension inequality.**  If `E_r^{a+vr r} = 0`, then
`dim E_r^a ≤ dim E_{r+1}^a + dim E_r^{a-vr r}`. -/
theorem finrank_le_next (S : CohSS 𝕜) {r : ℕ} (hr : 2 ≤ r) (a : ℤ × ℤ)
    (hfin : FiniteDimensional 𝕜 (S.E r a)) (hinf : FiniteDimensional 𝕜 (S.E r (a - vr r)))
    (hout : IsZero (S.E r (a + vr r))) :
    Module.finrank 𝕜 (S.E r a) ≤
      Module.finrank 𝕜 (S.E (r + 1) a) + Module.finrank 𝕜 (S.E r (a - vr r)) := by
  haveI := hfin
  haveI := hinf
  have hDz : (S.d r a (a + vr r)).hom = 0 :=
    congrArg (fun f : S.E r a ⟶ S.E r (a + vr r) => f.hom)
      (S.d_eq_zero_of_isZero (r := r) (a := a) (b := a + vr r) hout)
  have hrange : Module.finrank 𝕜 ↥(LinearMap.range (S.d r a (a + vr r)).hom) = 0 := by
    rw [hDz, LinearMap.range_zero, finrank_bot]
  have hD := LinearMap.finrank_range_add_finrank_ker (S.d r a (a + vr r)).hom
  have hK : Module.finrank 𝕜 (S.E r a)
      = Module.finrank 𝕜 ↥(LinearMap.ker (S.d r a (a + vr r)).hom) := by omega
  have hP := LinearMap.finrank_range_add_finrank_ker (S.proj r a)
  have htop : LinearMap.range (S.proj r a) = ⊤ := LinearMap.range_eq_top.mpr (S.proj_surj r a hr)
  have hfr : Module.finrank 𝕜 ↥(LinearMap.range (S.proj r a)) =
      Module.finrank 𝕜 (S.E (r + 1) a) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ htop ≪≫ₗ Submodule.topEquiv)
  -- the kernel of `proj` injects into the range of the incoming differential
  have hker : Module.finrank 𝕜 ↥(LinearMap.ker (S.proj r a))
      ≤ Module.finrank 𝕜 (S.E r (a - vr r)) := by
    let incl : ↥(LinearMap.ker (S.proj r a)) →ₗ[𝕜]
        ↥(LinearMap.range (S.d r (a - vr r) a).hom) :=
      { toFun := fun x => ⟨(x.1 : ↥(S.E r a)), (S.proj_ker r a hr x.1).mp x.2⟩
        map_add' := fun x y => by ext; rfl
        map_smul' := fun c x => by ext; rfl }
    have hinj : Function.Injective incl := by
      intro x y hxy
      have h2 : ((x.1 : ↥(S.E r a)) : S.E r a) = ((y.1 : ↥(S.E r a)) : S.E r a) :=
        congrArg (fun w : ↥(LinearMap.range (S.d r (a - vr r) a).hom) => (w : S.E r a)) hxy
      exact Subtype.ext (Subtype.ext h2)
    exact (LinearMap.finrank_le_finrank_of_injective hinj).trans
      (LinearMap.finrank_range_le (S.d r (a - vr r) a).hom)
  omega

/-- Monotonicity along the pages, iterated, inside the box. -/
theorem finrank_le_two (S : CohSS 𝕜) (N : ℕ)
    (hbox : ∀ a : ℤ × ℤ, 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ (N : ℤ) →
      FiniteDimensional 𝕜 (S.E 2 a))
    (a : ℤ × ℤ) (h1 : 0 ≤ a.1) (h2 : 0 ≤ a.2) (h3 : a.1 + a.2 ≤ (N : ℤ)) :
    ∀ k : ℕ, Module.finrank 𝕜 (S.E (k + 2) a) ≤ Module.finrank 𝕜 (S.E 2 a) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      exact (S.finrank_succ_le (r := k + 2) (by omega) a
        (S.finiteDimensional_E N hbox k a h1 h2 h3)).trans ih

/-- Monotonicity along the pages, iterated, in a negative bidegree (both sides vanish). -/
theorem finrank_le_two_of_neg (S : CohSS 𝕜) (a : ℤ × ℤ) (h : a.1 < 0 ∨ a.2 < 0) (k : ℕ) :
    Module.finrank 𝕜 (S.E (k + 2) a) ≤ Module.finrank 𝕜 (S.E 2 a) := by
  rw [S.finrank_eq_zero_of_neg (r := k + 2) h, S.finrank_eq_zero_of_neg (r := 2) h]

/-- **The telescoped dimension bound along the row `q = 0`.** -/
theorem finrank_row0_le (S : CohSS 𝕜) (N : ℕ)
    (hbox : ∀ a : ℤ × ℤ, 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ (N : ℤ) →
      FiniteDimensional 𝕜 (S.E 2 a))
    (n : ℕ) (hn : n ≤ N) :
    Module.finrank 𝕜 (S.E 2 ((n : ℤ), 0)) ≤
      Module.finrank 𝕜 (S.E (n + 2) ((n : ℤ), 0)) +
        ∑ r ∈ Finset.range n, Module.finrank 𝕜 (S.E 2 (sr n (r + 2))) := by
  have hfd := S.finiteDimensional_E N hbox
  -- finiteness of the source bidegrees, at page `2` and at page `k+2`
  have hbox' : ∀ k : ℕ, Module.finrank 𝕜 (S.E (k + 2) (sr n (k + 2))) ≤
      Module.finrank 𝕜 (S.E 2 (sr n (k + 2))) := by
    intro k
    by_cases h1 : 0 ≤ (sr n (k + 2)).1
    · by_cases h2 : 0 ≤ (sr n (k + 2)).2
      · refine S.finrank_le_two N hbox _ h1 h2 ?_ k
        simp only [sr, Prod.fst_sub, Prod.snd_sub, Prod.fst_ofNat, Prod.snd_ofNat]
        omega
      · exact S.finrank_le_two_of_neg _ (Or.inr (by omega)) k
    · exact S.finrank_le_two_of_neg _ (Or.inl (by omega)) k
  have hfd' : ∀ k : ℕ, FiniteDimensional 𝕜 (S.E (k + 2) (sr n (k + 2))) := by
    intro k
    by_cases h1 : 0 ≤ (sr n (k + 2)).1
    · by_cases h2 : 0 ≤ (sr n (k + 2)).2
      · exact hfd k _ h1 h2 (by
          simp only [sr, Prod.fst_sub, Prod.snd_sub, Prod.fst_ofNat, Prod.snd_ofNat]
          omega)
      · exact S.finiteDimensional_of_neg (Or.inr (by omega))
    · exact S.finiteDimensional_of_neg (Or.inl (by omega))
  have hstep : ∀ k : ℕ, Module.finrank 𝕜 (S.E (k + 2) ((n : ℤ), 0)) ≤
      Module.finrank 𝕜 (S.E (k + 3) ((n : ℤ), 0)) +
        Module.finrank 𝕜 (S.E 2 (sr n (k + 2))) := by
    intro k
    have hout : IsZero (S.E (k + 2) (((n : ℤ), (0 : ℤ)) + vr (k + 2))) := by
      refine S.isZero_quad (k + 2) _ (Or.inr ?_)
      simp only [vr, Prod.snd_add, Prod.snd_ofNat]
      omega
    have hfin1 : FiniteDimensional 𝕜 (S.E (k + 2) ((n : ℤ), 0)) :=
      hfd k _ (by simp) (by simp) (by simp; omega)
    have hfin2 : FiniteDimensional 𝕜 (S.E (k + 2) (sr n (k + 2))) := hfd' k
    have hfin2' : FiniteDimensional 𝕜 (S.E (k + 2) (((n : ℤ), (0 : ℤ)) - vr (k + 2))) := by
      rw [src_row0_eq n (k + 2)]
      exact hfin2
    have hmain := S.finrank_le_next (r := k + 2) (by omega) (((n : ℤ), (0 : ℤ))) hfin1 hfin2' hout
    rw [src_row0_eq] at hmain
    exact hmain.trans (add_le_add le_rfl (hbox' k))
  have key : ∀ k : ℕ, Module.finrank 𝕜 (S.E 2 ((n : ℤ), 0)) ≤
      Module.finrank 𝕜 (S.E (k + 2) ((n : ℤ), 0)) +
        ∑ r ∈ Finset.range k, Module.finrank 𝕜 (S.E 2 (sr n (r + 2))) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hstep k
        have hsum : ∑ r ∈ Finset.range (k + 1), Module.finrank 𝕜 (S.E 2 (sr n (r + 2))) =
            (∑ r ∈ Finset.range k, Module.finrank 𝕜 (S.E 2 (sr n (r + 2)))) +
              Module.finrank 𝕜 (S.E 2 (sr n (k + 2))) := Finset.sum_range_succ _ _
        have hidx : Module.finrank 𝕜 (S.E (k + 3) ((n : ℤ), 0)) =
            Module.finrank 𝕜 (S.E (k + 1 + 2) ((n : ℤ), 0)) := by norm_num
        rw [hidx] at hs
        rw [hsum]
        omega
  exact key n

/-- The class of `x` on the next page, when the target of the differential is zero (so that `x` is
a cycle). -/
noncomputable def nextClass (S : CohSS 𝕜) (r : ℕ) (a : ℤ × ℤ)
    (h : IsZero (S.E r (a + vr r))) (x : S.E r a) : S.E (r + 1) a :=
  S.proj r a ⟨x, by rw [S.d_eq_zero_of_isZero h]; rfl⟩

/-- The value of `nextClass` on any proof that `x` is a cycle. -/
theorem nextClass_eq_proj (S : CohSS 𝕜) (r : ℕ) (a : ℤ × ℤ) (h : IsZero (S.E r (a + vr r)))
    (x : S.E r a) (hx : (S.d r a (a + vr r)).hom x = 0) :
    S.nextClass r a h x = S.proj r a ⟨x, hx⟩ := by
  unfold nextClass
  exact congrArg (⇑(S.proj r a)) (Subtype.ext rfl)

/-- `nextClass` is onto the next page. -/
theorem nextClass_surjective (S : CohSS 𝕜) (r : ℕ) (hr : 2 ≤ r) (a : ℤ × ℤ)
    (h : IsZero (S.E r (a + vr r))) : Function.Surjective (S.nextClass r a h) := by
  intro y
  obtain ⟨x, hx⟩ := S.proj_surj r a hr y
  refine ⟨x.1, ?_⟩
  rw [S.nextClass_eq_proj r a h x.1 x.2]
  exact hx

/-- `nextClass x` vanishes exactly when `x` is hit by the incoming differential. -/
theorem nextClass_eq_zero_iff (S : CohSS 𝕜) (r : ℕ) (hr : 2 ≤ r) (a : ℤ × ℤ)
    (h : IsZero (S.E r (a + vr r))) (x : S.E r a) :
    S.nextClass r a h x = 0 ↔ x ∈ LinearMap.range (S.d r (a - vr r) a).hom := by
  rw [S.nextClass_eq_proj r a h x (by rw [S.d_eq_zero_of_isZero h]; rfl)]
  exact S.proj_ker r a hr ⟨x, _⟩

/-- If the next page vanishes, every class of `E_r^a` is the image of the incoming differential. -/
theorem exists_eq_of_isZero_next (S : CohSS 𝕜) (r : ℕ) (hr : 2 ≤ r) (a : ℤ × ℤ)
    (h : IsZero (S.E r (a + vr r))) (hzero : IsZero (S.E (r + 1) a)) (x : S.E r a) :
    x ∈ LinearMap.range (S.d r (a - vr r) a).hom := by
  haveI : Subsingleton (S.E (r + 1) a) := ModuleCat.subsingleton_of_isZero hzero
  have h0 : S.nextClass r a h x = 0 := Subsingleton.elim _ _
  exact (S.nextClass_eq_zero_iff r hr a h x).mp h0

/-- `nextClass` of a nonzero class is nonzero when nothing maps into `a`. -/
theorem nextClass_ne_zero_iff (S : CohSS 𝕜) (r : ℕ) (hr : 2 ≤ r) (a : ℤ × ℤ)
    (h : IsZero (S.E r (a + vr r))) (hsrc : IsZero (S.E r (a - vr r))) (x : S.E r a) :
    S.nextClass r a h x ≠ 0 ↔ x ≠ 0 := by
  have hz : (S.d r (a - vr r) a).hom = 0 :=
    congrArg (fun f : S.E r (a - vr r) ⟶ S.E r a => f.hom) (hsrc.eq_of_src _ _)
  have hrange : LinearMap.range (S.d r (a - vr r) a).hom = ⊥ := by rw [hz, LinearMap.range_zero]
  rw [ne_eq, S.nextClass_eq_zero_iff r hr a h x, hrange, Submodule.mem_bot, ne_eq]

/-- A nonzero cycle that nothing hits is nonzero on every later page. -/
theorem exists_ne_zero_iterate (S : CohSS 𝕜) {r : ℕ} (hr : 2 ≤ r) (a : ℤ × ℤ)
    (x : S.E r a) (hcyc : (S.d r a (a + vr r)).hom x = 0) (hx0 : x ≠ 0)
    (hsrc : ∀ k : ℕ, r ≤ k → IsZero (S.E k (a - vr k)))
    (htgt : ∀ k : ℕ, r + 1 ≤ k → IsZero (S.E k (a + vr k))) :
    ∀ t : ℕ, ∃ y : S.E (r + t) a, y ≠ 0 := by
  have aux : ∀ t : ℕ, ∃ y : S.E (r + t) a,
      (S.d (r + t) a (a + vr (r + t))).hom y = 0 ∧ y ≠ 0 := by
    intro t
    induction t with
    | zero =>
        refine ⟨x, ?_, hx0⟩
        simpa using hcyc
    | succ t ih =>
        obtain ⟨y, hyc, hy0⟩ := ih
        have hrt : 2 ≤ r + t := by omega
        let y' : S.E (r + t + 1) a := S.proj (r + t) a ⟨y, hyc⟩
        have hy'0 : y' ≠ 0 := by
          intro h0
          have hmem : y ∈ LinearMap.range (S.d (r + t) (a - vr (r + t)) a).hom :=
            (S.proj_ker (r + t) a hrt ⟨y, hyc⟩).mp h0
          obtain ⟨z, hz⟩ := hmem
          haveI : Subsingleton (S.E (r + t) (a - vr (r + t))) :=
            ModuleCat.subsingleton_of_isZero (hsrc (r + t) (by omega))
          have hz0 : z = 0 := Subsingleton.elim _ _
          rw [hz0, map_zero] at hz
          exact hy0 hz.symm
        refine ⟨y', ?_, hy'0⟩
        have hd : S.d (r + (t + 1)) a (a + vr (r + (t + 1))) = 0 :=
          S.d_eq_zero_of_isZero (r := r + (t + 1)) (a := a)
            (b := a + vr (r + (t + 1))) (htgt (r + t + 1) (by omega))
        rw [hd]
        rfl
  intro t
  obtain ⟨y, _, hy0⟩ := aux t
  exact ⟨y, by simpa [Nat.add_assoc] using hy0⟩

/-- A nonzero cycle that is never hit gives a nonzero class on the target page. -/
theorem not_isZero_of_survives (S : CohSS 𝕜) {r : ℕ} (hr : 2 ≤ r) (a : ℤ × ℤ)
    (x : S.E r a) (hcyc : (S.d r a (a + vr r)).hom x = 0) (hx0 : x ≠ 0)
    (hsrc : ∀ k : ℕ, r ≤ k → IsZero (S.E k (a - vr k)))
    (htgt : ∀ k : ℕ, r + 1 ≤ k → IsZero (S.E k (a + vr k))) (t : ℕ) :
    ¬ IsZero (S.E (r + t) a) := by
  obtain ⟨y, hy0⟩ := S.exists_ne_zero_iterate hr a x hcyc hx0 hsrc htgt t
  intro h
  exact hy0 ((ModuleCat.subsingleton_of_isZero h).allEq y 0)

end CohSS

/-- A pure tensor of nonzero vectors over a field is nonzero. -/
theorem tmul_ne_zero_of_ne_zero {𝕜 : Type} [Field 𝕜] {M N : Type} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] {m : M} {n : N} (hm : m ≠ 0) (hn : n ≠ 0) :
    m ⊗ₜ[𝕜] n ≠ 0 := by
  have hfun : ∀ {V : Type} [AddCommGroup V] [Module 𝕜 V] (v : V), v ≠ 0 →
      ∃ φ : V →ₗ[𝕜] 𝕜, φ v = 1 := by
    intro V _ _ v hv
    have hker : (LinearMap.toSpanSingleton 𝕜 V v).ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro c hc
      have hc' : c • v = 0 := hc
      rcases smul_eq_zero.mp hc' with h | h
      · exact h
      · exact absurd h hv
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
    refine ⟨g, ?_⟩
    have := congrArg (fun f : 𝕜 →ₗ[𝕜] 𝕜 => f 1) hg
    simpa [LinearMap.toSpanSingleton_apply] using this
  obtain ⟨ρ, hρ⟩ := hfun m hm
  obtain ⟨σ, hσ⟩ := hfun n hn
  intro hzero
  have h1 : (TensorProduct.lid 𝕜 𝕜) ((TensorProduct.map ρ σ) (m ⊗ₜ[𝕜] n)) = 1 := by
    rw [TensorProduct.map_tmul, TensorProduct.lid_tmul, hρ, hσ, one_smul]
  rw [hzero, map_zero, map_zero] at h1
  exact one_ne_zero h1.symm

end

end Work.Pi6
