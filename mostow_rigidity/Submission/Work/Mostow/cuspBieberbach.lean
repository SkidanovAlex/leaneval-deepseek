import Mathlib
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.twoLeOrth
import Submission.Work.Mostow.flatActProper
import Submission.Work.Mostow.flatActCocompact

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

noncomputable section

set_option linter.unusedVariables false

variable {n : ℕ}

/-!
# `cuspBieberbach`: the cusp stabiliser of a lattice contains `ℤ²`

Let `G ≤ PO n 1` (`n ≥ 3`) be a subgroup of the horospherical isometries at a boundary point
`ξ ∈ Sph n`: every `g ∈ G` fixes `ξ` and preserves the Busemann level `lev ξ`.  Suppose `G` acts
properly discontinuously (`hprop`) and cocompactly (`hcoc`) on the horosphere of level `D > 0`.
Then `G` contains two commuting elements generating a free abelian group of rank two.

The proof is Bieberbach's theorem applied to the flat action of `G` on `ξ^⊥ ≅ ℝ^{n-1}`:

* `Work.Mostow.cuspZ2Defs` provides the flat space `xiPerp ξ = (ℝξ)ᗮ`, the flat action
  `flatFun hξ D g` of `g` on it, and the group homomorphism `cuspFlatHom`
  `G →* (xiPerp ξ ≃ᵢ xiPerp ξ)`;
* transporting along a linear isometry equivalence `E (finrank ℝ (xiPerp ξ)) ≃ₗᵢ[ℝ] xiPerp ξ`
  gives `rhoHom : G →* (E (fdim ξ) ≃ᵢ E (fdim ξ))`, which is properly discontinuous
  (`rhoHom_proper`) and cocompact (`rhoHom_cocompact`) by the hypotheses `hprop`, `hcoc`;
* the kernel of `rhoHom` is trivial (`rhoHom_ker`): an element of `G` acting trivially on the
  level-`D` horosphere is the identity, because a point of `ℍⁿ` is determined by its level and
  its distances to all points of a horosphere (`horoDet`), a consequence of the horospherical
  formula for the hyperbolic distance (`Work.Mostow.levYcFormula`);
* Bieberbach's first theorem (`BieberbachProp`, imported as `hBb`) gives a finite-index subgroup
  of `rhoHom G` acting by translations whose translation vectors span, and `spanTopPair` extracts
  two independent translations, i.e. two commuting elements generating `ℤ²`.

All helper lemmas live in the namespace `Work.Mostow.CuspB` so that this module can be imported
alongside the other `Work.Mostow` developments without name clashes.
-/

namespace CuspB

theorem horoDet (n : ℕ) (ξ : E n) (hξ : ξ ∈ Sph n)
    (D : ℝ) (hD : 0 < D) {z z' : E n}
    (hz : lev ξ z = lev ξ z')
    (h : ∀ w : E n, lev ξ w = D → hdist z w = hdist z' w) : z = z' := by
  have hkey : ∀ y : E n, inner ℝ y ξ = 0 → ‖yc ξ z - y‖ = ‖yc ξ z' - y‖ := by
    intro y hy
    have hlevy : lev ξ (hptOf ξ y D) = D := (hptOfLevelYc ξ hξ hy hD).1
    have hycy : yc ξ (hptOf ξ y D) = y := (hptOfLevelYc ξ hξ hy hD).2.1
    have hd : hdist z (hptOf ξ y D) = hdist z' (hptOf ξ y D) := h _ hlevy
    have e1 := levYcFormula hξ z (hptOf ξ y D)
    have e2 := levYcFormula hξ z' (hptOf ξ y D)
    rw [hycy, hlevy, hd] at e1
    rw [hycy, hlevy, ← hz] at e2
    rw [e2] at e1
    have hcoef : (lev ξ z * D / 2) * ‖yc ξ z - y‖ ^ 2
        = (lev ξ z * D / 2) * ‖yc ξ z' - y‖ ^ 2 := (add_left_cancel e1).symm
    have hpos : 0 < lev ξ z * D / 2 := by
      have hp := lev_pos ξ hξ z
      positivity
    have hsq : ‖yc ξ z - y‖ ^ 2 = ‖yc ξ z' - y‖ ^ 2 :=
      mul_left_cancel₀ (ne_of_gt hpos) hcoef
    have h2 := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2
  have hinl : ∀ y : E n, inner ℝ y ξ = 0 → inner ℝ (yc ξ z - yc ξ z') y = 0 := by
    intro y hy
    have h1 : ‖yc ξ z - y‖ ^ 2 = ‖yc ξ z' - y‖ ^ 2 := by rw [hkey y hy]
    have h0 : ‖yc ξ z‖ ^ 2 = ‖yc ξ z'‖ ^ 2 := by
      simpa using hkey 0 (by simp)
    rw [norm_sub_sq_real, norm_sub_sq_real] at h1
    rw [h0] at h1
    have h2 : inner ℝ (yc ξ z) y = inner ℝ (yc ξ z') y := by linarith
    rw [inner_sub_left, h2, sub_self]
  have hp : yc ξ z = yc ξ z' := by
    have hmem : inner ℝ (yc ξ z - yc ξ z') ξ = 0 := by
      rw [inner_sub_left, inner_yc hξ z, inner_yc hξ z', sub_self]
    have h0 := hinl (yc ξ z - yc ξ z') hmem
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)
  have hz1 : hptOf ξ (yc ξ z) (lev ξ z) = z := hptOf_yc_lev hξ z
  have hz2 : hptOf ξ (yc ξ z') (lev ξ z') = z' := hptOf_yc_lev hξ z'
  rw [← hz1, ← hz2, hp, hz]

theorem spanTopPair {G : Type*} [Group G] {m : ℕ} (hm : 2 ≤ m)
    (rho : G →* (E m ≃ᵢ E m)) (hinj : Function.Injective rho) (T : Subgroup G) (v : G → E m)
    (hv : ∀ t ∈ T, ∀ x : E m, rho t x = x + v t)
    (hspan : Submodule.span ℝ (v '' (T : Set G)) = ⊤) :
    ∃ a b : G, a * b = b * a ∧ ∀ i j : ℤ, a ^ i * b ^ j = 1 → i = 0 ∧ j = 0 := by
  have hfin : Module.finrank ℝ (E m) = m := by rw [finrank_euclideanSpace, Fintype.card_fin]
  have hex : ∃ x₁ ∈ v '' (T : Set G), ∃ x₂ ∈ v '' (T : Set G),
      LinearIndependent ℝ ![x₁, x₂] := by
    obtain ⟨s₀, hs₀S, hs₀ne⟩ : ∃ s ∈ v '' (T : Set G), s ≠ 0 := by
      by_contra hc
      push_neg at hc
      have hbot : Submodule.span ℝ (v '' (T : Set G)) = ⊥ := by
        rw [Submodule.span_eq_bot]
        intro x hx
        exact hc x hx
      have h0 : Module.finrank ℝ (E m) = 0 := by
        have h1 : (⊤ : Submodule ℝ (E m)) = ⊥ := by rw [← hspan, hbot]
        have h2 : Module.finrank ℝ (⊤ : Submodule ℝ (E m))
            = Module.finrank ℝ (⊥ : Submodule ℝ (E m)) := by rw [h1]
        rw [finrank_top] at h2
        simpa [finrank_bot] using h2
      omega
    obtain ⟨s₁, hs₁S, hs₁⟩ : ∃ s ∈ v '' (T : Set G),
        s ∉ Submodule.span ℝ ({s₀} : Set (E m)) := by
      by_contra hc
      push_neg at hc
      have hle : Submodule.span ℝ (v '' (T : Set G)) ≤ Submodule.span ℝ ({s₀} : Set (E m)) :=
        Submodule.span_le.mpr hc
      have h1 : Module.finrank ℝ (Submodule.span ℝ ({s₀} : Set (E m))) = 1 :=
        finrank_span_singleton hs₀ne
      have h2 : Module.finrank ℝ (E m) ≤ 1 := by
        have h3 : Module.finrank ℝ (E m)
            = Module.finrank ℝ (Submodule.span ℝ (v '' (T : Set G))) := by
          rw [hspan, finrank_top]
        rw [h3]
        exact le_trans (Submodule.finrank_mono hle) (le_of_eq h1)
      omega
    refine ⟨s₀, hs₀S, s₁, hs₁S, ?_⟩
    rw [LinearIndependent.pair_iff]
    intro c d hcd
    by_contra hne
    have hd : d ≠ 0 := by
      rintro rfl
      simp only [zero_smul, add_zero] at hcd
      exact hne ⟨(smul_eq_zero.mp hcd).resolve_right hs₀ne, rfl⟩
    refine hs₁ (Submodule.mem_span_singleton.mpr ⟨-(c / d), ?_⟩)
    have h4 : d • s₁ = -(c • s₀) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hcd
    have h5 : s₁ = d⁻¹ • (-(c • s₀)) := by
      calc s₁ = d⁻¹ • (d • s₁) := (inv_smul_smul₀ hd s₁).symm
        _ = d⁻¹ • (-(c • s₀)) := by rw [h4]
    rw [h5, ← neg_smul, smul_smul]
    congr 1
    rw [div_eq_mul_inv]
    ring
  obtain ⟨x₁, hx₁, x₂, hx₂, hli⟩ := hex
  obtain ⟨t₀, ht₀T, ht₀⟩ := hx₁
  obtain ⟨t₁, ht₁T, ht₁⟩ := hx₂
  rw [← ht₀, ← ht₁] at hli
  have hadd : ∀ s t : T, v (((s * t : T) : G)) = v ((s : G)) + v ((t : G)) := by
    intro s t
    have h1 : rho (((s * t : T) : G)) = rho (s : G) * rho (t : G) := by
      rw [Subgroup.coe_mul, map_mul]
    have h2 := congrArg (fun e : E m ≃ᵢ E m => e 0) h1
    rw [IsometryEquiv.mul_apply, hv ((s : T) : G) s.2, hv ((t : T) : G) t.2,
      hv (((s * t : T) : G)) (s * t).2] at h2
    simp only [zero_add] at h2
    rw [add_comm] at h2
    exact h2
  let ψ : Additive T →+ E m :=
    { toFun := fun s => v ((s.toMul : T) : G)
      map_zero' := by
        have h2 := hv (1 : G) (one_mem T) 0
        have h1 := congrArg (fun e : E m ≃ᵢ E m => e 0) (map_one rho)
        rw [h1] at h2
        simpa using h2.symm
      map_add' := by
        intro s t
        exact hadd s.toMul t.toMul }
  have hψz : ∀ (t : T) (k : ℤ), ψ (Additive.ofMul (t ^ k)) = k • v (t : G) := by
    intro t k
    rw [ofMul_zpow, map_zsmul]
    rfl
  refine ⟨(t₀ : G), (t₁ : G), ?_, ?_⟩
  · apply hinj
    apply IsometryEquiv.ext
    intro x
    simp only [map_mul, IsometryEquiv.mul_apply, hv (t₀ : G) ht₀T, hv (t₁ : G) ht₁T]
    abel
  · intro i j hij
    have hT : (⟨(t₀ : G), ht₀T⟩ : T) ^ i * (⟨(t₁ : G), ht₁T⟩ : T) ^ j = 1 := by
      apply Subtype.ext
      have h1 : T.subtype ((⟨(t₀ : G), ht₀T⟩ : T) ^ i) = (t₀ : G) ^ i :=
        map_zpow T.subtype ⟨(t₀ : G), ht₀T⟩ i
      have h2 : T.subtype ((⟨(t₁ : G), ht₁T⟩ : T) ^ j) = (t₁ : G) ^ j :=
        map_zpow T.subtype ⟨(t₁ : G), ht₁T⟩ j
      have h3 : T.subtype ((⟨(t₀ : G), ht₀T⟩ : T) ^ i * (⟨(t₁ : G), ht₁T⟩ : T) ^ j)
          = T.subtype (1 : T) := by
        rw [map_mul, h1, h2, map_one]
        exact hij
      simpa using h3
    have h1 : ψ (Additive.ofMul ((⟨(t₀ : G), ht₀T⟩ : T) ^ i
        * (⟨(t₁ : G), ht₁T⟩ : T) ^ j)) = 0 := by
      rw [hT, ofMul_one]
      have h2 := hv (1 : G) (one_mem T) 0
      have h3 := congrArg (fun e : E m ≃ᵢ E m => e 0) (map_one rho)
      rw [h3] at h2
      simpa using h2.symm
    have h2 : ψ (Additive.ofMul ((⟨(t₀ : G), ht₀T⟩ : T) ^ i
        * (⟨(t₁ : G), ht₁T⟩ : T) ^ j)) = i • v (t₀ : G) + j • v (t₁ : G) := by
      rw [ofMul_mul, map_add, hψz _ i, hψz _ j]
    have h3 : i • v (t₀ : G) + j • v (t₁ : G) = 0 := by rw [← h2]; exact h1
    have h3' : (i : ℝ) • v (t₀ : G) + (j : ℝ) • v (t₁ : G) = 0 := by
      simpa only [Int.cast_smul_eq_zsmul] using h3
    have h4 := (LinearIndependent.pair_iff.mp hli) (i : ℝ) (j : ℝ) h3'
    exact ⟨by exact_mod_cast h4.1, by exact_mod_cast h4.2⟩

/-! ## The Euclidean structure on `ξ^⊥` -/

/-- dimension of the flat space `ξ^⊥`. -/
abbrev fdim (ξ : E n) : ℕ := Module.finrank ℝ (xiPerp ξ)

noncomputable def fEquiv (ξ : E n) : E (fdim ξ) ≃ₗᵢ[ℝ] xiPerp ξ :=
  (stdOrthonormalBasis ℝ (xiPerp ξ)).repr.symm

noncomputable def fIso (ξ : E n) : E (fdim ξ) ≃ᵢ xiPerp ξ := (fEquiv ξ).toIsometryEquiv

lemma fIso_norm (ξ : E n) (x : E (fdim ξ)) : ‖fIso ξ x‖ = ‖x‖ := by
  rw [← Submodule.norm_coe (fIso ξ x)]
  exact (fEquiv ξ).norm_map x

lemma fIso_symm_norm (ξ : E n) (y : xiPerp ξ) : ‖(fIso ξ).symm y‖ = ‖y‖ := by
  rw [← fIso_norm ξ ((fIso ξ).symm y), IsometryEquiv.apply_symm_apply]

lemma fIso_cont (ξ : E n) : Continuous (fun x : E (fdim ξ) => ((fIso ξ x : xiPerp ξ) : E n)) :=
  continuous_subtype_val.comp (fIso ξ).continuous

/-! ## The flat action transported to `E (fdim ξ)` -/

def rhoHom (hA : POBasic n) (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n) (D : ℝ)
    (hD : 0 < D) (G : Subgroup (PO n 1))
    (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u) :
    G →* (E (fdim ξ) ≃ᵢ E (fdim ξ)) where
  toFun g := ((fIso ξ).trans (cuspFlatHom (ξ := ξ) hA (HypIsoData.ofProp hI) hξ D hD G hlev g)).trans
    (fIso ξ).symm
  map_one' := by
    apply IsometryEquiv.ext
    intro x
    rw [IsometryEquiv.trans_apply, IsometryEquiv.trans_apply, map_one]
    simp
  map_mul' g₁ g₂ := by
    apply IsometryEquiv.ext
    intro x
    simp only [IsometryEquiv.trans_apply, IsometryEquiv.mul_apply,
      IsometryEquiv.apply_symm_apply, map_mul]

lemma rhoHom_apply_eq (hA : POBasic n) (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (D : ℝ) (hD : 0 < D) (G : Subgroup (PO n 1))
    (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u) (g : G) (x : E (fdim ξ)) :
    rhoHom hA hI ξ hξ D hD G hlev g x =
      (fIso ξ).symm (flatFun hξ D (g : PO n 1) (fIso ξ x)) := by
  show ((fIso ξ).trans
      (cuspFlatHom (ξ := ξ) hA (HypIsoData.ofProp hI) hξ D hD G hlev g)).trans (fIso ξ).symm x = _
  rw [IsometryEquiv.trans_apply, IsometryEquiv.trans_apply]
  rfl

/-! ## Properness -/

lemma rhoHom_proper (hA : POBasic n) (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (D : ℝ) (hD : 0 < D) (G : Subgroup (PO n 1))
    (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (hprop : ∀ u₀ : E n, lev ξ u₀ = D → ∀ K : Set (E n), IsCompact K →
      {g : G | (g : PO n 1) • u₀ ∈ K}.Finite) :
    ∀ K : Set (E (fdim ξ)), IsCompact K →
      {g : G | ((rhoHom hA hI ξ hξ D hD G hlev g) '' K ∩ K).Nonempty}.Finite := by
  intro K hK
  have hK' : IsCompact ((fun x : E (fdim ξ) => ((fIso ξ x : xiPerp ξ) : E n)) '' K) :=
    hK.image (fIso_cont ξ)
  have hKW : ∀ y ∈ (fun x : E (fdim ξ) => ((fIso ξ x : xiPerp ξ) : E n)) '' K,
      inner ℝ y ξ = 0 := by
    rintro y ⟨x, -, rfl⟩
    exact xiPerp_inner' (fIso ξ x)
  refine (flatActProper n hI ξ hξ D hD G hlev hprop _ hK' hKW).subset ?_
  rintro g ⟨x, hxρ, hxK⟩
  obtain ⟨x₀, hx₀K, rfl⟩ := hxρ
  refine ⟨((fIso ξ x₀ : xiPerp ξ) : E n), ⟨x₀, hx₀K, rfl⟩,
    ((fIso ξ (rhoHom hA hI ξ hξ D hD G hlev g x₀) : xiPerp ξ) : E n),
    ⟨rhoHom hA hI ξ hξ D hD G hlev g x₀, hxK, rfl⟩, ?_⟩
  rw [rhoHom_apply_eq, IsometryEquiv.apply_symm_apply]
  rfl

/-! ## Cocompactness -/

lemma rhoHom_cocompact (hA : POBasic n) (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (D : ℝ) (hD : 0 < D) (G : Subgroup (PO n 1))
    (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (hcoc : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = D →
      ∃ g : G, (g : PO n 1) • u ∈ K) :
    ∃ K : Set (E (fdim ξ)), IsCompact K ∧ ∀ x : E (fdim ξ),
      ∃ g : G, rhoHom hA hI ξ hξ D hD G hlev g x ∈ K := by
  obtain ⟨R, hR⟩ := flatActCocompact n hI ξ hξ D hD G hlev hcoc
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, fun x => ?_⟩
  obtain ⟨g, hg⟩ := hR ((fIso ξ x : xiPerp ξ) : E n) (xiPerp_inner' (fIso ξ x))
  refine ⟨g, ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, rhoHom_apply_eq, fIso_symm_norm]
  have h2 : ‖flatFun hξ D (g : PO n 1) (fIso ξ x)‖ =
      ‖yc ξ ((g : PO n 1) • hptOf ξ ((fIso ξ x : xiPerp ξ) : E n) D)‖ := by
    rw [← Submodule.norm_coe (flatFun hξ D (g : PO n 1) (fIso ξ x))]
    rfl
  rw [h2]
  exact hg

/-! ## Triviality of the kernel -/

lemma rhoHom_ker (hA : POBasic n) (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (D : ℝ) (hD : 0 < D) (G : Subgroup (PO n 1))
    (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u) :
    ∀ k : G, rhoHom hA hI ξ hξ D hD G hlev k = 1 → k = 1 := by
  intro k hk
  have hfun : ∀ y : xiPerp ξ, flatFun hξ D (k : PO n 1) y = y := by
    intro y
    have h1 : rhoHom hA hI ξ hξ D hD G hlev k ((fIso ξ).symm y) = (fIso ξ).symm y := by
      rw [hk]; rfl
    have h2 := congrArg (fIso ξ) h1
    rwa [rhoHom_apply_eq, IsometryEquiv.apply_symm_apply, IsometryEquiv.apply_symm_apply] at h2
  have htriv : ∀ w : E n, lev ξ w = D → (k : PO n 1) • w = w := by
    intro w hw
    have hymem : yc ξ w ∈ xiPerp ξ :=
      mem_xiPerp_iff.mpr (by rw [real_inner_comm]; exact inner_yc hξ w)
    have h3 : yc ξ ((k : PO n 1) • hptOf ξ (yc ξ w) D) = yc ξ w := by
      have := congrArg (fun z : xiPerp ξ => (z : E n)) (hfun ⟨yc ξ w, hymem⟩)
      simpa using this
    have hw' : hptOf ξ (yc ξ w) D = w := by
      rw [← hw]
      exact hptOf_yc_lev hξ w
    have hlev' : lev ξ ((k : PO n 1) • hptOf ξ (yc ξ w) D) = D := by
      rw [hlev k k.2 (hptOf ξ (yc ξ w) D),
        (hptOfLevelYc ξ hξ (xiPerp_inner' ⟨yc ξ w, hymem⟩) hD).1]
    calc (k : PO n 1) • w = (k : PO n 1) • hptOf ξ (yc ξ w) D := by rw [hw']
      _ = hptOf ξ (yc ξ ((k : PO n 1) • hptOf ξ (yc ξ w) D)) D :=
            (hptOf_yc ξ hξ D hD _ hlev').symm
      _ = hptOf ξ (yc ξ w) D := by rw [h3]
      _ = w := hw'
  have hone : (k : PO n 1) = 1 := hA.faithful (k : PO n 1) (fun u => horoDet n ξ hξ D hD
    (hlev k k.2 u)
    (fun w hw => by
      calc hdist ((k : PO n 1) • u) w
          = hdist ((k : PO n 1) • u) ((k : PO n 1) • w) := by rw [htriv w hw]
        _ = hdist u w := (HypIsoData.ofProp hI).isom_smul _ _ _))
  exact Subtype.ext hone

end CuspB

open CuspB

theorem cuspBieberbach (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (ξ : E n) (hξ : ξ ∈ Sph n) (D : ℝ) (hD : 0 < D)
    (G : Subgroup (PO n 1)) (hfix : ∀ g ∈ G, bd g ξ = ξ)
    (hlev : ∀ g ∈ G, ∀ u : E n, lev ξ (g • u) = lev ξ u)
    (hprop : ∀ u₀ : E n, lev ξ u₀ = D → ∀ K : Set (E n), IsCompact K →
        {g : G | (g : PO n 1) • u₀ ∈ K}.Finite)
    (hcoc : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, lev ξ u = D →
        ∃ g : G, (g : PO n 1) • u ∈ K) :
    ∃ a b : G, a * b = b * a ∧ (∀ i j : ℤ, a ^ i * b ^ j = 1 → i = 0 ∧ j = 0) := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hm : 2 ≤ fdim ξ := twoLeOrth n hn ξ hξ
  have hpd := rhoHom_proper hA' hI ξ hξ D hD G hlev hprop
  have hcc := rhoHom_cocompact hA' hI ξ hξ D hD G hlev hcoc
  obtain ⟨T, v, -, hv, hspan⟩ := hBb (fdim ξ) G (rhoHom hA' hI ξ hξ D hD G hlev) hpd hcc
  have hinj : Function.Injective (rhoHom hA' hI ξ hξ D hD G hlev) := by
    intro g h hgh
    have h1 : rhoHom hA' hI ξ hξ D hD G hlev (g * h⁻¹) = 1 := by
      rw [map_mul, map_inv, hgh, mul_inv_cancel]
    have h2 : g * h⁻¹ = 1 := rhoHom_ker hA' hI ξ hξ D hD G hlev (g * h⁻¹) h1
    have h3 := congrArg (fun x : G => x * h) h2
    simpa [mul_assoc] using h3
  exact spanTopPair hm (rhoHom hA' hI ξ hξ D hD G hlev) hinj T v hv hspan

end

end Work.Mostow
