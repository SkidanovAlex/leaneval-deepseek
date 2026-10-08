import Mathlib
import Submission.Work.Higman.Family
import Submission.Work.Hering.HardCore.fix_eq_of_ne_refl
import Submission.Work.Hering.HardCore.bCocycle_sqForm_expansion
import Submission.Work.Hering.HardCore.smul_coord_of_det_ne_zero
import Submission.Work.Hering.HardCore.det_ne_zero_of_independent

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Hering.HardCore

open Work.Higman

abbrev F8 := GaloisField 2 3

/-! ### Algebra of the `B`-cocycle -/

/-- The squaring form `q u = b u u` of Higman's `B`-cocycle. -/
def sqForm (F : Type*) [Field F] (θ : F ≃+* F) (ε : F) (u : F × F) : F :=
  bCocycle F θ ε u u

/-- The polar form `p u v = b u v + b v u` of `q`. -/
def polForm (F : Type*) [Field F] (θ : F ≃+* F) (ε : F) (u v : F × F) : F :=
  bCocycle F θ ε u v + bCocycle F θ ε v u

lemma bCocycle_smul_left (F : Type*) [Field F] (θ : F ≃+* F) (ε r : F) (u v : F × F) :
    bCocycle F θ ε (r • u) v = r * bCocycle F θ ε u v := by
  simp only [bCocycle, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring_nf

lemma bCocycle_smul_right (F : Type*) [Field F] (θ : F ≃+* F) (ε r : F) (u v : F × F) :
    bCocycle F θ ε u (r • v) = θ r * bCocycle F θ ε u v := by
  simp only [bCocycle, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul]
  ring_nf

lemma bCocycle_add_left (F : Type*) [Field F] (θ : F ≃+* F) (ε : F) (u u' v : F × F) :
    bCocycle F θ ε (u + u') v = bCocycle F θ ε u v + bCocycle F θ ε u' v := by
  simp only [bCocycle, Prod.fst_add, Prod.snd_add, add_mul]
  ring

lemma bCocycle_add_right (F : Type*) [Field F] (θ : F ≃+* F) (ε : F) (u v v' : F × F) :
    bCocycle F θ ε u (v + v') = bCocycle F θ ε u v + bCocycle F θ ε u v' := by
  simp only [bCocycle, Prod.fst_add, Prod.snd_add, map_add, mul_add]
  ring

lemma sqForm_smul (F : Type*) [Field F] (θ : F ≃+* F) (ε r : F) (u : F × F) :
    sqForm F θ ε (r • u) = r * θ r * sqForm F θ ε u := by
  simp only [sqForm, bCocycle, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul]
  ring_nf

lemma polForm_smul_self (F : Type*) [Field F] (θ : F ≃+* F) (ε r : F) (u : F × F) :
    polForm F θ ε u (r • u) = (r + θ r) * sqForm F θ ε u := by
  simp only [polForm, sqForm, bCocycle, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul]
  ring_nf

lemma sqForm_add (F : Type*) [Field F] (θ : F ≃+* F) (ε : F) (u v : F × F) :
    sqForm F θ ε (u + v) = sqForm F θ ε u + sqForm F θ ε v + polForm F θ ε u v := by
  simp only [sqForm, polForm, bCocycle, Prod.fst_add, Prod.snd_add, map_add, mul_add, add_mul]
  ring_nf

/-! ### Facts about `GaloisField 2 3` -/

lemma f8_card : Nat.card F8 = 8 := by
  rw [GaloisField.card 2 3 (by norm_num : (3 : ℕ) ≠ 0)]
  norm_num

lemma f8_exists_ne_zero_ne_one : ∃ r : F8, r ≠ 0 ∧ r ≠ 1 := by
  classical
  by_contra h
  have h' : ∀ r : F8, r ≠ 0 → r = 1 := by
    intro r hr
    by_contra hr1
    exact h ⟨r, hr, hr1⟩
  haveI : Fintype F8 := Fintype.ofFinite F8
  have hsub : (Finset.univ : Finset F8) ⊆ ({0, 1} : Finset F8) := by
    intro x _
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
    · simp [h' x hx]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Finset.card_pair (by norm_num : (0 : F8) ≠ 1)] at h1
  have h2 : Fintype.card F8 = 8 := by rw [← Nat.card_eq_fintype_card, f8_card]
  omega

/-! ### The main theorem -/

set_option maxHeartbeats 1000000 in
theorem noIsotropic_B3 :
    ∀ (θ : GaloisField 2 3 ≃+* GaloisField 2 3) (ε : GaloisField 2 3),
      θ ≠ RingEquiv.refl _
      → (∀ a b : GaloisField 2 3, a * θ a + ε * (a * θ b) + b * θ b = 0 → a = 0 ∧ b = 0)
      → ¬ ∃ W : Submodule (ZMod 2) (GaloisField 2 3 × GaloisField 2 3),
          Module.finrank (ZMod 2) W = 3 ∧
          (∀ u v : W, Work.Higman.bCocycle (GaloisField 2 3) θ ε u.1 v.1 =
            Work.Higman.bCocycle (GaloisField 2 3) θ ε v.1 u.1) := by
  intro θ ε hθ haniso
  rintro ⟨W, hdim, hiso⟩
  -- (0) the polar form vanishes on W
  have hpol : ∀ x y : W, polForm F8 θ ε (x : F8 × F8) (y : F8 × F8) = 0 := by
    intro x y
    rw [polForm, hiso x y]
    exact CharTwo.add_self_eq_zero _
  -- (1) if `x ∈ W`, `x ≠ 0` and `r • x ∈ W` then `r ∈ {0,1}`
  have hkey : ∀ (x : F8 × F8), x ∈ W → x ≠ 0 → ∀ r : F8, r • x ∈ W → r = 0 ∨ r = 1 := by
    intro x hx hx0 r hr
    have h1 : polForm F8 θ ε x (r • x) = 0 := hpol ⟨x, hx⟩ ⟨r • x, hr⟩
    have h2 : polForm F8 θ ε x (r • x) = (r + θ r) * sqForm F8 θ ε x :=
      polForm_smul_self F8 θ ε r x
    have hxq : sqForm F8 θ ε x ≠ 0 := by
      intro hzero
      have hz : x.1 * θ x.1 + ε * (x.1 * θ x.2) + x.2 * θ x.2 = 0 := hzero
      obtain ⟨h1', h2'⟩ := haniso x.1 x.2 hz
      exact hx0 (Prod.ext h1' h2')
    have h3 : (r + θ r) * sqForm F8 θ ε x = 0 := by rw [← h2, h1]
    have h4 : r + θ r = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h hxq
    have h5 : θ r = r := by
      have h6 := neg_eq_of_add_eq_zero_left h4
      rwa [CharTwo.neg_eq] at h6
    exact fix_eq_of_ne_refl θ hθ r h5
  -- (2) two nonzero elements of `W`, which are automatically `F`-independent
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h] at hdim
    have hz : Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) (F8 × F8)) = 0 := by
      simp
    rw [hz] at hdim
    exact absurd hdim (by norm_num)
  obtain ⟨u, huW, hu0⟩ := (Submodule.ne_bot_iff W).mp hWne
  have hvex : ∃ v ∈ W, v ∉ (ZMod 2 ∙ u : Submodule (ZMod 2) (F8 × F8)) := by
    by_contra h
    have hle : W ≤ (ZMod 2 ∙ u : Submodule (ZMod 2) (F8 × F8)) := fun x hx => by
      by_contra hxS
      exact h ⟨x, hx, hxS⟩
    have hfin : Module.finrank (ZMod 2) (ZMod 2 ∙ u : Submodule (ZMod 2) (F8 × F8)) = 1 :=
      finrank_span_singleton hu0
    have h2 := Submodule.finrank_mono hle
    rw [hdim, hfin] at h2
    omega
  obtain ⟨v, hvW, hvu⟩ := hvex
  have hv0 : v ≠ 0 := fun h => hvu (h.symm ▸ Submodule.zero_mem _)
  have hne : v ≠ u :=
    fun h => hvu (h.symm ▸ (Submodule.mem_span_singleton).mpr ⟨1, one_smul _ _⟩)
  have hfindep : ∀ a b : F8, a • u + b • v = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have hb0 : b = 0 := by
      by_contra hb
      have h22 : b • v + b • v = 0 := by
        rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
      have h1 : b • v = a • u := by
        have h6 := neg_eq_of_add_eq_zero_left hab
        rwa [neg_eq_of_add_eq_zero_left h22] at h6
      have hvv : v = (b⁻¹ * a) • u := by
        calc v = b⁻¹ • (b • v) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
          _ = b⁻¹ • (a • u) := by rw [h1]
          _ = (b⁻¹ * a) • u := by rw [smul_smul]
      have hmem : (b⁻¹ * a) • u ∈ W := hvv ▸ hvW
      rcases hkey u huW hu0 (b⁻¹ * a) hmem with h | h
      · rw [h, zero_smul] at hvv
        exact hv0 hvv
      · rw [h, one_smul] at hvv
        exact hne hvv
    subst hb0
    refine ⟨?_, rfl⟩
    have hau : a • u = 0 := by simpa using hab
    have h1 : a * u.1 = 0 := by
      have hh := congr_arg Prod.fst hau
      simpa only [Prod.smul_fst, Prod.zero_eq_mk, smul_eq_mul] using hh
    have h2 : a * u.2 = 0 := by
      have hh := congr_arg Prod.snd hau
      simpa only [Prod.smul_snd, Prod.zero_eq_mk, smul_eq_mul] using hh
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · rcases mul_eq_zero.mp h2 with h' | h'
      · exact h'
      · exact absurd (Prod.ext h h') hu0
  -- (3) a third element of `W` outside the `𝔽₂`-span of `u` and `v`
  have hlin2 : LinearIndependent (ZMod 2) ![u, v] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg2 : g 0 • u + g 1 • v = 0 := by
      simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using hg
    have hg' : (algebraMap (ZMod 2) F8 (g 0)) • u + (algebraMap (ZMod 2) F8 (g 1)) • v = 0 := by
      rw [IsScalarTower.algebraMap_smul F8 (g 0) u,
        IsScalarTower.algebraMap_smul F8 (g 1) v]
      exact hg2
    obtain ⟨h0, h1⟩ := hfindep _ _ hg'
    intro i
    fin_cases i
    · exact FaithfulSMul.algebraMap_injective (ZMod 2) F8 (by simpa using h0)
    · exact FaithfulSMul.algebraMap_injective (ZMod 2) F8 (by simpa using h1)
  have hrange : Set.range ![u, v] = ({u, v} : Set (F8 × F8)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hspan2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({u, v} : Set (F8 × F8))) = 2 := by
    have h := finrank_span_eq_card hlin2
    rw [Fintype.card_fin] at h
    rwa [hrange] at h
  obtain ⟨w, hwW, hwS⟩ : ∃ w ∈ W, w ∉ Submodule.span (ZMod 2) ({u, v} : Set (F8 × F8)) := by
    by_contra h
    have hle : W ≤ Submodule.span (ZMod 2) ({u, v} : Set (F8 × F8)) := fun x hx => by
      by_contra hxS
      exact h ⟨x, hx, hxS⟩
    have h2 := Submodule.finrank_mono hle
    rw [hdim, hspan2] at h2
    omega
  -- (4) coordinates of `w` in the `F`-basis `(u, v)`
  have hdet : u.1 * v.2 - u.2 * v.1 ≠ 0 := det_ne_zero_of_independent u v hfindep
  set lam : F8 := (w.1 * v.2 - w.2 * v.1) / (u.1 * v.2 - u.2 * v.1) with hlam
  set mu : F8 := (u.1 * w.2 - u.2 * w.1) / (u.1 * v.2 - u.2 * v.1) with hmu
  have hw : lam • u + mu • v = w := by
    rw [hlam, hmu]
    exact smul_coord_of_det_ne_zero u v w hdet
  -- (5) abbreviations
  set A : F8 := bCocycle F8 θ ε u u with hA
  set B : F8 := bCocycle F8 θ ε v v with hB
  set C : F8 := bCocycle F8 θ ε u v with hC
  have hCvu : bCocycle F8 θ ε v u = C := by
    rw [hC]
    exact (hiso ⟨u, huW⟩ ⟨v, hvW⟩).symm
  set al : F8 := lam + θ lam with hal
  set be : F8 := mu + θ mu with hbe
  have hA0 : A ≠ 0 := by
    intro hzero
    rw [hA, bCocycle] at hzero
    obtain ⟨h1', h2'⟩ := haniso u.1 u.2 hzero
    exact hu0 (Prod.ext h1' h2')
  have hB0 : B ≠ 0 := by
    intro hzero
    rw [hB, bCocycle] at hzero
    obtain ⟨h1', h2'⟩ := haniso v.1 v.2 hzero
    exact hv0 (Prod.ext h1' h2')
  -- (6) the two linear conditions
  have hcond1 : A * al + C * be = 0 := by
    have hwu : bCocycle F8 θ ε w u + bCocycle F8 θ ε u w = 0 := by
      simpa only [polForm] using hpol ⟨w, hwW⟩ ⟨u, huW⟩
    have e1 : bCocycle F8 θ ε w u = lam * bCocycle F8 θ ε u u + mu * bCocycle F8 θ ε v u := by
      rw [← hw, bCocycle_add_left, bCocycle_smul_left, bCocycle_smul_left]
    have e2 : bCocycle F8 θ ε u w
        = θ lam * bCocycle F8 θ ε u u + θ mu * bCocycle F8 θ ε u v := by
      rw [← hw, bCocycle_add_right, bCocycle_smul_right, bCocycle_smul_right]
    rw [e1, e2, hCvu] at hwu
    rw [← hA, ← hC] at hwu
    rw [hal, hbe]
    ring_nf at hwu ⊢
    exact hwu
  have hcond2 : B * be + C * al = 0 := by
    have hwv : bCocycle F8 θ ε w v + bCocycle F8 θ ε v w = 0 := by
      simpa only [polForm] using hpol ⟨w, hwW⟩ ⟨v, hvW⟩
    have e1 : bCocycle F8 θ ε w v = lam * bCocycle F8 θ ε u v + mu * bCocycle F8 θ ε v v := by
      rw [← hw, bCocycle_add_left, bCocycle_smul_left, bCocycle_smul_left]
    have e2 : bCocycle F8 θ ε v w
        = θ lam * bCocycle F8 θ ε v u + θ mu * bCocycle F8 θ ε v v := by
      rw [← hw, bCocycle_add_right, bCocycle_smul_right, bCocycle_smul_right]
    rw [e1, e2, hCvu] at hwv
    rw [← hB, ← hC] at hwv
    rw [hal, hbe]
    ring_nf at hwv ⊢
    exact hwv
  -- (7) `al ≠ 0` and `be ≠ 0`
  have hspan_uv : ∀ c d : F8, (c = 0 ∨ c = 1) → (d = 0 ∨ d = 1) →
      c • u + d • v ∈ Submodule.span (ZMod 2) ({u, v} : Set (F8 × F8)) := by
    intro c d hc hd
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · simp
    · simpa using Submodule.subset_span (show v ∈ ({u, v} : Set (F8 × F8)) by simp)
    · simpa using Submodule.subset_span (show u ∈ ({u, v} : Set (F8 × F8)) by simp)
    · simpa using Submodule.add_mem _
        (Submodule.subset_span (show u ∈ ({u, v} : Set (F8 × F8)) by simp))
        (Submodule.subset_span (show v ∈ ({u, v} : Set (F8 × F8)) by simp))
  have hspan_fix : ∀ c d : F8, θ c = c → θ d = d →
      c • u + d • v ∈ Submodule.span (ZMod 2) ({u, v} : Set (F8 × F8)) :=
    fun c d hc hd => hspan_uv c d (fix_eq_of_ne_refl θ hθ c hc)
      (fix_eq_of_ne_refl θ hθ d hd)
  have hal0 : al ≠ 0 := by
    intro halz
    have halz' : lam + θ lam = 0 := by rw [← hal]; exact halz
    have hCbe : C * be = 0 := by
      have h := hcond1
      rw [halz, mul_zero, zero_add] at h
      exact h
    rcases eq_or_ne be 0 with hbez | hbenz
    · have hlam' : θ lam = lam := by
        have h6 := neg_eq_of_add_eq_zero_left halz'
        rwa [CharTwo.neg_eq] at h6
      have hbez' : mu + θ mu = 0 := by rw [← hbe]; exact hbez
      have hmu' : θ mu = mu := by
        have h6 := neg_eq_of_add_eq_zero_left hbez'
        rwa [CharTwo.neg_eq] at h6
      exact hwS (hw ▸ hspan_fix lam mu hlam' hmu')
    · have hC0 : C = 0 := by
        rcases mul_eq_zero.mp hCbe with h | h
        · exact h
        · exact absurd h hbenz
      have hBbe : B * be = 0 := by
        have h := hcond2
        rw [hC0, zero_mul, add_zero] at h
        exact h
      have hB0' : B = 0 := by
        rcases mul_eq_zero.mp hBbe with h | h
        · exact h
        · exact absurd h hbenz
      exact hB0 hB0'
  have hbe0 : be ≠ 0 := by
    intro hbez
    have hbez' : mu + θ mu = 0 := by rw [← hbe]; exact hbez
    have hCal : C * al = 0 := by
      have h := hcond2
      rw [hbez, mul_zero, zero_add] at h
      exact h
    rcases eq_or_ne al 0 with halz | halnz
    · have hmu' : θ mu = mu := by
        have h6 := neg_eq_of_add_eq_zero_left hbez'
        rwa [CharTwo.neg_eq] at h6
      have halz' : lam + θ lam = 0 := by rw [← hal]; exact halz
      have hlam' : θ lam = lam := by
        have h6 := neg_eq_of_add_eq_zero_left halz'
        rwa [CharTwo.neg_eq] at h6
      exact hwS (hw ▸ hspan_fix lam mu hlam' hmu')
    · have hC0 : C = 0 := by
        rcases mul_eq_zero.mp hCal with h | h
        · exact h
        · exact absurd h halnz
      have hAal : A * al = 0 := by
        have h := hcond1
        rw [hC0, zero_mul, add_zero] at h
        exact h
      have hA0' : A = 0 := by
        rcases mul_eq_zero.mp hAal with h | h
        · exact h
        · exact absurd h halnz
      exact hA0 hA0'
  -- (8) `A = C * γ`, `B = C * γ⁻¹` for `γ = be / al`
  set γ : F8 := be / al with hγ
  have hγ0 : γ ≠ 0 := div_ne_zero hbe0 hal0
  have hAeq : A = C * γ := by
    have h1' : A * al = C * be := by
      have h := hcond1
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
      exact h
    rw [hγ, ← mul_div_assoc]
    exact (eq_div_iff hal0).mpr h1'
  have hBeq : B = C * γ⁻¹ := by
    have h2' : B * be = C * al := by
      have h := hcond2
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
      exact h
    have hinv : γ⁻¹ = al / be := by rw [hγ, inv_div]
    rw [hinv, ← mul_div_assoc]
    exact (eq_div_iff hbe0).mpr h2'
  -- (9) contradiction: `q (u + γ • v) = 0` with `u + γ • v ≠ 0`
  have hfinal : sqForm F8 θ ε (u + γ • v) = 0 := by
    have hexp := bCocycle_sqForm_expansion θ ε 1 γ u v
    rw [one_smul] at hexp
    have hgoal : A + θ γ * C + γ * C + (γ * θ γ) * B = 0 := by
      have hcancel : (γ * θ γ) * (C * γ⁻¹) = C * θ γ := by
        calc (γ * θ γ) * (C * γ⁻¹) = C * θ γ * (γ * γ⁻¹) := by ring
          _ = C * θ γ := by rw [mul_inv_cancel₀ hγ0, mul_one]
      rw [hAeq, hBeq, hcancel]
      rw [show C * γ + θ γ * C + γ * C + C * θ γ =
        (C * γ + C * γ) + (θ γ * C + θ γ * C) by ring]
      rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    have key : (1 * θ 1) * bCocycle F8 θ ε u u + (1 * θ γ) * bCocycle F8 θ ε u v +
        (γ * θ 1) * bCocycle F8 θ ε v u + (γ * θ γ) * bCocycle F8 θ ε v v = 0 := by
      simp only [map_one, mul_one, one_mul, hCvu, ← hA, ← hB, ← hC]
      exact hgoal
    rw [sqForm, hexp]
    exact key
  have hne0 : u + γ • v ≠ 0 := by
    intro h
    have hh := hfindep 1 γ (by rw [one_smul]; exact h)
    exact one_ne_zero hh.1
  have hctr := haniso (u + γ • v).1 (u + γ • v).2
    (by simpa only [sqForm, bCocycle] using hfinal)
  exact hne0 (Prod.ext hctr.1 hctr.2)

end Work.Hering.HardCore
