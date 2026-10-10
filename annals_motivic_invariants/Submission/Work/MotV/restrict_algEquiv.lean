import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotT.RouteVCorollaries

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option maxHeartbeats 2000000

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero IntermediateField

/-- **The restriction of a `𝕜`-isomorphism of twist fields to `K = RatFunc 𝕜` is a `𝕜`-algebra
automorphism of `K`** (node NAT, surjectivity half).  Here `F_h = twistFieldT D h ⊆ Om D = K̄(E)`
is the T-twist field and `REG` is `K` algebraically closed in `F_{h₁}`
(`Work.MotT.twistFieldT_regular`, module `Submission.Work.MotT.RouteVCorollaries`).

Route.
1. `φ₀ c := Classical.choose (hθ c) : RatFunc 𝕜 →ₐ[𝕜] RatFunc 𝕜` with
   `hφ₀ : ∀ c, θ (algebraMap (RatFunc 𝕜) F₁ c) = algebraMap (RatFunc 𝕜) F₂ (φ₀ c)`; all
   `𝕜`-algebra homs between fields are injective, so it suffices to prove `φ₀` surjective.
2. **Key claim**: `t := RatFunc.X ∈ S := φ₀.fieldRange`.  (`S` is an `𝕜`-IntermediateField of `K`
   containing `t`, hence contains `𝕜⟮t⟯ = K` by `RatFunc.adjoin_X` and
   `IntermediateField.adjoin_le_iff`.)
3. `IsAlgebraic ↥S t`.  `S = 𝕜⟮f⟯` for `f = φ₀ t` (`AlgHom.fieldRange_eq_map`,
   `IntermediateField.adjoin_map`, `RatFunc.adjoin_X`).  With `A = f.num`, `B = f.denom ∈ 𝕜[Y]`
   (`RatFunc.num_div_denom`, `RatFunc.monic_denom`, `RatFunc.denom_ne_zero`),
   `Ψ := C ⟨f,_⟩ * B.map (algebraMap 𝕜 ↥S) - A.map (algebraMap 𝕜 ↥S) ∈ (↥S)[Y]` is *nonzero* and
   `aeval t Ψ = 0` (`Polynomial.aeval_map_algebraMap`, `Polynomial.aeval_C`, and
   `f * aeval t B = aeval t A`); non-vanishing is the only non-formal point — `Ψ = 0` forces
   `natDegree A = natDegree B` (`Polynomial.natDegree_C_mul`,
   `Polynomial.natDegree_map_eq_of_injective`) and comparing `leadingCoeff`s, with `B` monic, gives
   `f = algebraMap 𝕜 K (leadingCoeff A) ∈ 𝕜`, contradicting `RatFunc.transcendental_X` transported
   along the injective `φ₀` (`isAlgebraic_algHom_iff`).  (Alternative: `RatFunc.finrank_eq_max_natDegree`
   together with `Module.rank_lt_aleph0_iff` and `Algebra.IsAlgebraic.of_finite`.)
4. **Transport along `θ`.**  Put `z := θ.symm (algebraMap (RatFunc 𝕜) F₂ t) ∈ F₁`.  From a nonzero
   `p ∈ (↥S)[Y]` with `aeval t p = 0` (step 3) choose `c_i : K` with `φ₀ c_i = (p.coeff i : K)`
   (using `S = φ₀.fieldRange` and `AlgHom.mem_fieldRange`).  Then `q := ∑ i, C (c_i) * Y^i ∈ K[Y]`
   is nonzero and `aeval z q = 0`: apply `θ.symm` to the identity `∑ (p.coeff i : K) * t^i = 0` in
   `F₂ ⊇ K` and use `hφ₀`.
5. So `IsAlgebraic (RatFunc 𝕜) z`, and `Work.MotT.twistFieldT_regular D hD hk h₁ h₁0` gives `c` with
   `algebraMap K F₁ c = z`; applying `θ` gives `algebraMap K F₂ (φ₀ c) = algebraMap K F₂ t`, so
   `φ₀ c = t` and `t ∈ S` (injectivity of `algebraMap (RatFunc 𝕜) F₂`).
6. `AlgEquiv.ofBijective φ₀ ⟨injective, surjective⟩` finishes.  (`h₂0` is unused.) -/theorem restrict_algEquiv {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (hD : D.Good)
    (hk : ringChar 𝕜 ≠ 5) {h₁ h₂ : RatFunc 𝕜} (h₁0 : h₁ ≠ 0) (h₂0 : h₂ ≠ 0)
    (θ : Work.MotV.twistFieldT D h₁ ≃ₐ[𝕜] Work.MotV.twistFieldT D h₂)
    (hθ : ∀ c : RatFunc 𝕜, ∃ d, θ (algebraMap (RatFunc 𝕜) _ c)
      = algebraMap (RatFunc 𝕜) _ d) :
    ∃ φ : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜,
      ∀ c : RatFunc 𝕜, θ (algebraMap (RatFunc 𝕜) _ c) = algebraMap (RatFunc 𝕜) _ (φ c) := by
  classical
  let ψ : RatFunc 𝕜 → RatFunc 𝕜 := fun c => Classical.choose (hθ c)
  have hψ : ∀ c, θ (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (ψ c) :=
    fun c => Classical.choose_spec (hθ c)
  have hinj₂ : Function.Injective (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂)) :=
    RingHom.injective _
  have hψ_one : ψ 1 = 1 := by
    refine hinj₂ ?_
    rw [← hψ 1]
    simp
  have hψ_zero : ψ 0 = 0 := by
    refine hinj₂ ?_
    rw [← hψ 0]
    simp
  have hψ_add : ∀ a b, ψ (a + b) = ψ a + ψ b := by
    intro a b
    refine hinj₂ ?_
    calc algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (ψ (a + b))
        = θ (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) (a + b)) := (hψ (a + b)).symm
      _ = θ (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) a
              + algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) b) := by rw [map_add]
      _ = θ (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) a)
            + θ (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) b) := by rw [map_add]
      _ = algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (ψ a)
            + algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (ψ b) := by rw [hψ a, hψ b]
      _ = algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (ψ a + ψ b) := by rw [map_add]
  have hψ_mul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    refine hinj₂ ?_
    calc algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (ψ (a * b))
        = θ (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) (a * b)) := (hψ (a * b)).symm
      _ = θ (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) a
              * algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) b) := by rw [map_mul]
      _ = θ (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) a)
            * θ (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) b) := by rw [map_mul]
      _ = algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (ψ a)
            * algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (ψ b) := by rw [hψ a, hψ b]
      _ = algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (ψ a * ψ b) := by rw [map_mul]
  have hψ_comm : ∀ r : 𝕜, ψ (algebraMap 𝕜 (RatFunc 𝕜) r) = algebraMap 𝕜 (RatFunc 𝕜) r := by
    intro r
    refine hinj₂ ?_
    calc algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (ψ (algebraMap 𝕜 (RatFunc 𝕜) r))
        = θ (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁)
              (algebraMap 𝕜 (RatFunc 𝕜) r)) := (hψ _).symm
      _ = θ (algebraMap 𝕜 (Work.MotV.twistFieldT D h₁) r) := by
            rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (↥(Work.MotV.twistFieldT D h₁))]
      _ = algebraMap 𝕜 (Work.MotV.twistFieldT D h₂) r := θ.commutes r
      _ = algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂)
              (algebraMap 𝕜 (RatFunc 𝕜) r) := (IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜)
                (↥(Work.MotV.twistFieldT D h₂)) r).symm
  let φ₀ : RatFunc 𝕜 →ₐ[𝕜] RatFunc 𝕜 :=
    AlgHom.mk ({ toFun := ψ, map_one' := hψ_one, map_mul' := hψ_mul, map_zero' := hψ_zero, map_add' := hψ_add } : RatFunc 𝕜 →+* RatFunc 𝕜) hψ_comm
  have hφ₀ : ∀ c, θ (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) c)
      = algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (φ₀ c) := hψ
  have hinj₀ : Function.Injective φ₀ := RingHom.injective _
  let f : RatFunc 𝕜 := φ₀ RatFunc.X
  have hf_ne_C : ¬∃ c, f = RatFunc.C c := by
    rintro ⟨c, hc⟩
    have hc' : f = algebraMap 𝕜 (RatFunc 𝕜) c := by rw [hc, RatFunc.algebraMap_eq_C]
    have hc'' : φ₀ (RatFunc.X : RatFunc 𝕜) = algebraMap 𝕜 (RatFunc 𝕜) c := hc'
    have ht : (RatFunc.X : RatFunc 𝕜) = algebraMap 𝕜 (RatFunc 𝕜) c := by
      apply hinj₀
      rw [hc'', φ₀.commutes c]
    have halg : IsAlgebraic 𝕜 (algebraMap 𝕜 (RatFunc 𝕜) c) :=
      ⟨Polynomial.X - Polynomial.C c,
        Polynomial.X_sub_C_ne_zero c, by simp⟩
    exact RatFunc.transcendental_X (ht ▸ halg)
  have hle : (𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)) ≤ φ₀.fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro x rfl
    exact AlgHom.mem_fieldRange.mpr ⟨RatFunc.X, rfl⟩
  have hge : φ₀.fieldRange ≤ (𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)) := by
    rw [AlgHom.fieldRange_eq_map]
    refine IntermediateField.map_le_iff_le_comap.mpr ?_
    have h : (𝕜⟮(RatFunc.X : RatFunc 𝕜)⟯ : IntermediateField 𝕜 (RatFunc 𝕜))
        ≤ IntermediateField.comap φ₀ (𝕜⟮f⟯) := by
      rw [IntermediateField.adjoin_le_iff]
      rintro x rfl
      exact IntermediateField.mem_adjoin_simple_self 𝕜 f
    rwa [RatFunc.adjoin_X] at h
  let g₀ : RatFunc 𝕜 →ₐ[𝕜] ↥(𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)) :=
    φ₀.codRestrict (𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)).toSubalgebra
      (fun x => hge (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))
  have hg₀_inj : Function.Injective g₀ := fun a b h => hinj₀ (congrArg Subtype.val h)
  have hg₀_surj : Function.Surjective g₀ := by
    intro s
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.mp (hle s.2)
    exact ⟨x, Subtype.ext hx⟩
  let e : RatFunc 𝕜 ≃ₐ[𝕜] ↥(𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)) :=
    AlgEquiv.ofBijective g₀ ⟨hg₀_inj, hg₀_surj⟩
  have he : ∀ s : ↥(𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)),
      φ₀ (e.symm s) = (s : RatFunc 𝕜) := by
    intro s
    have h1 : e (e.symm s) = s := AlgEquiv.apply_symm_apply e s
    have h2 : (e (e.symm s)).val = φ₀ (e.symm s) := rfl
    rw [h1] at h2
    exact h2.symm
  obtain ⟨p, hp0, hp⟩ := RatFunc.isAlgebraic_adjoin_simple_X f hf_ne_C
  let g : ↥(𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)) →+* RatFunc 𝕜 := e.symm
  let q : Polynomial (RatFunc 𝕜) := p.map g
  have hg_inj : Function.Injective g := fun a b h => e.symm.injective h
  have hq_ne : q ≠ 0 := by
    intro hzero
    have hzero' : p.map g = 0 := hzero
    exact hp0 ((Polynomial.map_eq_zero_iff hg_inj).mp hzero')
  let z : ↥(Work.MotV.twistFieldT D h₁) :=
    θ.symm (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (RatFunc.X : RatFunc 𝕜))
  have hθz : θ z
      = algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (RatFunc.X : RatFunc 𝕜) := by
    simp only [z, AlgEquiv.apply_symm_apply]
  let G : ↥(𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)) →+* ↥(Work.MotV.twistFieldT D h₁) :=
    (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁)).comp g
  have hGs : ∀ s : ↥(𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)),
      G s = (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁)) (e.symm s) := fun s => rfl
  have hgi : ∀ s : ↥(𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)),
      g s = e.symm s := fun s => rfl
  have hq_aeval : Polynomial.aeval z q = 0 := by
    have h1 : Polynomial.aeval z q = p.eval₂ G z := by
      show Polynomial.aeval z (p.map g) = p.eval₂ G z
      rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have h2 : θ (p.eval₂ G z) = p.eval₂ (θ.toRingHom.comp G) (θ z) :=
      Polynomial.hom_eval₂ p G θ.toRingHom z
    have h3 : θ.toRingHom.comp G
        = (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂)).comp
            (algebraMap ↥(𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)) (RatFunc 𝕜)) := by
      ext s
      simp only [RingHom.comp_apply]
      rw [hGs s]
      have hs : (algebraMap ↥(𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)) (RatFunc 𝕜)) s
          = φ₀ (e.symm s) := (he s).symm
      rw [hs]
      exact congrArg Subtype.val (hφ₀ (e.symm s))
    have h5 : (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂))
          (Polynomial.aeval (RatFunc.X) p)
        = p.eval₂ ((algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂)).comp
            (algebraMap ↥(𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)) (RatFunc 𝕜)))
            ((algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂)) (RatFunc.X)) := by
      rw [Polynomial.aeval_def]
      exact Polynomial.hom_eval₂ p (algebraMap ↥(𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜))
        (RatFunc 𝕜)) (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂)) (RatFunc.X)
    have hmain : θ (Polynomial.aeval z q) = 0 := by
      calc θ (Polynomial.aeval z q) = θ (p.eval₂ G z) := by rw [h1]
        _ = p.eval₂ (θ.toRingHom.comp G) (θ z) := h2
        _ = p.eval₂ ((algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂)).comp
              (algebraMap ↥(𝕜⟮f⟯ : IntermediateField 𝕜 (RatFunc 𝕜)) (RatFunc 𝕜)))
              ((algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂)) (RatFunc.X)) := by
              rw [h3, hθz]
        _ = (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂))
              (Polynomial.aeval (RatFunc.X) p) := h5.symm
        _ = 0 := by rw [hp, map_zero]
    exact θ.injective (by rw [hmain, map_zero])
  have hz_alg : IsAlgebraic (RatFunc 𝕜) z := ⟨q, hq_ne, hq_aeval⟩
  obtain ⟨c, hc⟩ := Work.MotT.twistFieldT_regular D hD hk h₁ h₁0 z hz_alg
  have ht_mem : (RatFunc.X : RatFunc 𝕜) ∈ φ₀.fieldRange := by
    refine AlgHom.mem_fieldRange.mpr ⟨c, ?_⟩
    refine hinj₂ ?_
    calc algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (φ₀ c)
        = θ (algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₁) c) := (hφ₀ c).symm
      _ = θ z := by rw [hc]
      _ = algebraMap (RatFunc 𝕜) (Work.MotV.twistFieldT D h₂) (RatFunc.X) := hθz
  have htop : φ₀.fieldRange = ⊤ := by
    rw [eq_top_iff]
    have h : (𝕜⟮(RatFunc.X : RatFunc 𝕜)⟯ : IntermediateField 𝕜 (RatFunc 𝕜)) ≤ φ₀.fieldRange :=
      IntermediateField.adjoin_le_iff.mpr (by rintro x rfl; exact ht_mem)
    rwa [RatFunc.adjoin_X] at h
  have hsurj : Function.Surjective φ₀ := by
    intro y
    have hy : y ∈ φ₀.fieldRange := by rw [htop]; trivial
    exact AlgHom.mem_fieldRange.mp hy
  have hbij : Function.Bijective φ₀ := ⟨hinj₀, hsurj⟩
  refine ⟨AlgEquiv.ofBijective φ₀ hbij, ?_⟩
  intro c
  rw [AlgEquiv.ofBijective_apply]
  exact hφ₀ c

end Work.MotV
