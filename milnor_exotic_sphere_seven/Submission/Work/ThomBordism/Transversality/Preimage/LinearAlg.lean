import Mathlib
import Submission.Work.Surgery.BoundaryInstances

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Linear algebra for the transverse-preimage charts

Three elementary splitting lemmas used by the construction of the manifold structure on the
transverse preimage `F ⁻¹' X.core`:

* `exists_linearEquiv_prod_ker`: a surjective continuous linear map `ℝ^{(m+1)+k} → ℝ^k` is the
  first component of a linear equivalence `ℝ^{(m+1)+k} ≃ ℝ^k × ℝ^{m+1}`;
* `exists_linearEquiv_coord'`: a nonzero linear functional on a finite-dimensional space of
  dimension `n+1` is the zeroth coordinate in a suitable linear equivalence with `ℝ^{n+1}`;
* `exists_linearEquiv_prod_coord`: the second component of the splitting equivalence can moreover
  be arranged to agree with a prescribed functional `s` on the kernel of `a`, provided `s` does not
  vanish identically there.

The third lemma is what produces the "half-space coordinate" of the chart of the preimage at a
point of `∂M`: in the coordinates of the submersion normal form of `Φ ∘ F`, the level set is an
affine subspace `{a = c}` of dimension `9`, and the boundary hyperplane is `{z 0 = 0}`, so the
chart must identify the level-set coordinate system with the half-space in such a way that the
zeroth coordinate of the model is the restriction of `z ↦ z 0`.
-/

open scoped Manifold
open LinearMap

namespace Work.ThomBordism.Transversality.Preimage

noncomputable section

/-- **Splitting a surjection**: a surjective continuous linear map
`a : ℝ^{(m+1)+k} → ℝ^k` is the first component of a continuous linear equivalence
`ℝ^{(m+1)+k} ≃ ℝ^k × ℝ^{m+1}`. -/
theorem exists_linearEquiv_prod_ker (m k : ℕ)
    (a : EuclideanSpace ℝ (Fin ((m + k) + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (ha : Function.Surjective a) :
    ∃ T : EuclideanSpace ℝ (Fin ((m + k) + 1)) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (m + 1))),
      ∀ v, (T v).1 = a v := by
  let al : EuclideanSpace ℝ (Fin ((m + k) + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) := a
  have hZ : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+1))) = m + 1 := by
    rw [finrank_euclideanSpace]; simp
  have hker_fin : Module.finrank ℝ ↥al.ker = m + 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker al
    have hr : Module.finrank ℝ ↥al.range = k := by
      have htop : al.range = ⊤ := LinearMap.range_eq_top.mpr ha
      rw [htop, (Submodule.topEquiv).finrank_eq, finrank_euclideanSpace]
      simp
    have hV : Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+k)+1))) = (m+k) + 1 := by
      rw [finrank_euclideanSpace]; simp
    rw [hr, hV] at h
    omega
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl al.ker
  have hkerq : al.ker ⊓ q = ⊥ := hq.inf_eq_bot
  have hinj : Function.Injective (al.comp q.subtype) := by
    intro x y hxy
    have hmem : ((x : EuclideanSpace ℝ (Fin ((m+k)+1))) - (y : _)) ∈ al.ker ⊓ q := by
      constructor
      · change al ((x : _) - (y : _)) = 0
        simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hxy
        rw [map_sub, hxy, sub_self]
      · exact q.sub_mem x.2 y.2
    rw [hkerq, Submodule.mem_bot] at hmem
    exact Subtype.ext (sub_eq_zero.mp hmem)
  have hsurj_q : Function.Surjective (al.comp q.subtype) := by
    intro y
    obtain ⟨v, hv⟩ := ha y
    have hv' : v ∈ al.ker ⊔ q := by rw [hq.sup_eq_top]; trivial
    rw [Submodule.mem_sup] at hv'
    obtain ⟨p, hp, z, hz, hpz⟩ := hv'
    refine ⟨⟨z, hz⟩, ?_⟩
    have hp0 : al p = 0 := hp
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    calc al z = al (p + z) := by rw [map_add, hp0, zero_add]
      _ = al v := by rw [hpz]
      _ = y := hv
  let eqq : ↥q ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k) := LinearEquiv.ofBijective _ ⟨hinj, hsurj_q⟩
  let ep : ↥al.ker ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hker_fin, hZ])
  let e : (↥al.ker × ↥q) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin ((m+k)+1)) :=
    Submodule.prodEquivOfIsCompl _ q hq
  let e' : EuclideanSpace ℝ (Fin ((m+k)+1)) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (m+1))) :=
    e.symm.trans ((ep.prodCongr eqq).trans (LinearEquiv.prodComm ℝ _ _))
  have hecoe : ∀ x : ↥al.ker × ↥q,
      (e x : EuclideanSpace ℝ (Fin ((m+k)+1))) = ((x.1 : ↥al.ker) : _) + ((x.2 : ↥q) : _) := by
    intro x
    have h := Submodule.coe_prodEquivOfIsCompl al.ker q hq
    have h2 : (al.ker.prodEquivOfIsCompl q hq) x = (al.ker.subtype.coprod q.subtype) x := by
      rw [← h]; rfl
    rw [show e = al.ker.prodEquivOfIsCompl q hq from rfl, h2, LinearMap.coprod_apply]
    rfl
  refine ⟨e'.toContinuousLinearEquiv, ?_⟩
  intro v
  change (e' v).1 = a v
  have h1 : ((e' v).1 : EuclideanSpace ℝ (Fin k)) = eqq (e.symm v).2 := by
    simp only [e', LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.prodComm_apply,
      Prod.fst_swap]
  have h2 : (eqq (e.symm v).2 : EuclideanSpace ℝ (Fin k)) = al ((e.symm v).2 : _) := rfl
  have hv : v = ((e.symm v).1 : EuclideanSpace ℝ (Fin ((m+k)+1))) + ((e.symm v).2 : _) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply e v]
    exact hecoe (e.symm v)
  have hvv : ((e.symm v).2 : EuclideanSpace ℝ (Fin ((m+k)+1))) + ((e.symm v).1 : _) = v :=
    (add_comm _ _).trans hv.symm
  rw [h1, h2]
  calc al ((e.symm v).2 : EuclideanSpace ℝ (Fin ((m+k)+1)))
      = al (((e.symm v).2 : _) + ((e.symm v).1 : _)) := by
        rw [map_add, (e.symm v).1.2, add_zero]
    _ = al v := by rw [hvv]
    _ = a v := rfl

/-- **A nonzero functional is a coordinate**: if `σ : W →ₗ[ℝ] ℝ` is a nonzero linear functional on a
finite-dimensional real vector space of dimension `n+1`, there is a linear equivalence
`W ≃ₗ ℝ^{n+1}` whose zeroth coordinate is `σ`. -/
theorem exists_linearEquiv_coord' {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (σ : W →ₗ[ℝ] ℝ) (hσ : σ ≠ 0)
    (hdim : Module.finrank ℝ W = n + 1) :
    ∃ S : W ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)), ∀ w, (S w) 0 = σ w := by
  obtain ⟨w₀, hw₀⟩ : ∃ w, σ w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hσ (LinearMap.ext h)
  obtain ⟨u, hu⟩ : ∃ u, σ u = 1 := ⟨(σ w₀)⁻¹ • w₀, by
    rw [map_smul, smul_eq_mul]; exact inv_mul_cancel₀ hw₀⟩
  have hsurj : Function.Surjective σ := fun t => ⟨t • u, by rw [map_smul, hu, smul_eq_mul, mul_one]⟩
  have hKfin : Module.finrank ℝ ↥(LinearMap.ker σ) = n := by
    have h := LinearMap.finrank_range_add_finrank_ker σ
    have hr : Module.finrank ℝ ↥(LinearMap.range σ) = 1 := by
      rw [LinearMap.range_eq_top.mpr hsurj, (Submodule.topEquiv).finrank_eq, Module.finrank_self]
    rw [hr, hdim] at h
    omega
  let s₀ : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (0 : Fin (n+1))).comp
      (Work.Surgery.euclToPi (n+1)).toContinuousLinearMap
  have hs₀ : ∀ v : EuclideanSpace ℝ (Fin (n+1)), s₀ v = v.ofLp 0 := by
    intro v
    simp [s₀, Work.Surgery.euclToPi_ofLp]
  have hs₀surj : Function.Surjective s₀ := by
    intro t
    refine ⟨Work.Surgery.piToEucl (n+1) (Pi.single 0 t), ?_⟩
    rw [hs₀, Work.Surgery.ofLp_piToEucl, Pi.single_eq_same]
  have hZfin : Module.finrank ℝ ↥(LinearMap.ker (s₀ : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] ℝ)) = n := by
    have h := LinearMap.finrank_range_add_finrank_ker (s₀ : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] ℝ)
    have hr : Module.finrank ℝ ↥(LinearMap.range (s₀ : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] ℝ)) = 1 := by
      rw [LinearMap.range_eq_top.mpr hs₀surj, (Submodule.topEquiv).finrank_eq, Module.finrank_self]
    have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n + 1 := by
      rw [finrank_euclideanSpace]; simp
    rw [hr, hE] at h
    omega
  let θ : ↥(LinearMap.ker σ) ≃ₗ[ℝ]
      ↥(LinearMap.ker (s₀ : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] ℝ)) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hKfin, hZfin])
  let e0 : EuclideanSpace ℝ (Fin (n+1)) := Work.Surgery.e₀ n
  have he0 : e0.ofLp 0 = (1:ℝ) := Work.Surgery.e₀_apply_zero n
  have hθ0 : ∀ z : ↥(LinearMap.ker σ),
      (((θ z : ↥(LinearMap.ker (s₀ : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] ℝ))) :
        EuclideanSpace ℝ (Fin (n+1)))).ofLp 0 = 0 := by
    intro z
    have hz : s₀ ((θ z : ↥(LinearMap.ker (s₀ : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] ℝ))) :
        EuclideanSpace ℝ (Fin (n+1))) = 0 := (θ z).2
    rw [hs₀] at hz
    exact hz
  let U : W →ₗ[ℝ] ↥(LinearMap.ker σ) :=
    { toFun := fun w => ⟨w - (σ w) • u, by
        show σ (w - (σ w) • u) = 0
        rw [map_sub, map_smul, hu, smul_eq_mul, mul_one, sub_self]⟩
      map_add' := fun a b => by
        refine Subtype.ext ?_
        simp only [map_add, add_smul, Submodule.coe_add]
        abel
      map_smul' := fun c a => by
        refine Subtype.ext ?_
        simp only [map_smul, smul_sub, Submodule.coe_smul, smul_smul, smul_eq_mul,
          RingHom.id_apply] }
  let S₀ : W →ₗ[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
    { toFun := fun w => (σ w) • e0 + ((θ (U w) :
        ↥(LinearMap.ker (s₀ : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] ℝ))) :
          EuclideanSpace ℝ (Fin (n+1)))
      map_add' := fun a b => by
        have hU : U (a + b) = U a + U b := map_add U a b
        have hσ : σ (a + b) = σ a + σ b := map_add σ a b
        rw [hU, hσ, map_add, add_smul]
        simp only [Submodule.coe_add]
        abel
      map_smul' := fun c a => by
        have hU : U (c • a) = c • U a := map_smul U c a
        have hσ : σ (c • a) = c * σ a := by rw [map_smul, smul_eq_mul]
        rw [hU, hσ, map_smul, smul_add, smul_smul]
        simp only [Submodule.coe_smul, RingHom.id_apply] }
  refine ⟨LinearEquiv.ofBijective S₀ ⟨?_, ?_⟩, ?_⟩
  · intro a b hab
    have h0a : (S₀ a).ofLp 0 = σ a := by
      simp only [S₀, LinearMap.coe_mk, AddHom.coe_mk]
      rw [PiLp.add_apply, PiLp.smul_apply, he0, smul_eq_mul, mul_one, hθ0, add_zero]
    have h0b : (S₀ b).ofLp 0 = σ b := by
      simp only [S₀, LinearMap.coe_mk, AddHom.coe_mk]
      rw [PiLp.add_apply, PiLp.smul_apply, he0, smul_eq_mul, mul_one, hθ0, add_zero]
    have hσeq : σ a = σ b := by
      have h : (S₀ a).ofLp 0 = (S₀ b).ofLp 0 := by rw [hab]
      rwa [h0a, h0b] at h
    have hθab : θ (U a) = θ (U b) := by
      have h := hab
      simp only [S₀, LinearMap.coe_mk, AddHom.coe_mk] at h
      rw [hσeq] at h
      exact Subtype.ext (add_left_cancel h)
    have hUab : U a = U b := θ.injective hθab
    have hsub : a - b = 0 := by
      have h1 : U (a - b) = 0 := by rw [map_sub U a b, hUab, sub_self]
      have h2 : ((U (a - b) : ↥(LinearMap.ker σ)) : W) = 0 := by rw [h1]; rfl
      simp only [U, LinearMap.coe_mk, AddHom.coe_mk] at h2
      rw [map_sub, sub_eq_zero.mpr hσeq, zero_smul, sub_zero] at h2
      exact h2
    exact sub_eq_zero.mp hsub
  · intro v
    set t : ℝ := v.ofLp 0 with ht
    have hz : v - t • e0 ∈ LinearMap.ker (s₀ : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] ℝ) := by
      show s₀ (v - t • e0) = 0
      rw [hs₀, PiLp.sub_apply, PiLp.smul_apply, he0, smul_eq_mul, mul_one]
      exact sub_self t
    refine ⟨t • u + (θ.symm ⟨v - t • e0, hz⟩ : W), ?_⟩
    have hσt : σ (t • u + (θ.symm ⟨v - t • e0, hz⟩ : W)) = t := by
      rw [map_add, map_smul, hu, smul_eq_mul, mul_one]
      have : σ ((θ.symm ⟨v - t • e0, hz⟩ : ↥(LinearMap.ker σ)) : W) = 0 :=
        (θ.symm ⟨v - t • e0, hz⟩).2
      rw [this, add_zero]
    have hUt : U (t • u + (θ.symm ⟨v - t • e0, hz⟩ : W)) = θ.symm ⟨v - t • e0, hz⟩ := by
      refine Subtype.ext ?_
      simp only [U, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, Submodule.coe_smul]
      rw [hσt]
      abel
    have hmain : S₀ (t • u + (θ.symm ⟨v - t • e0, hz⟩ : W)) = v := by
      simp only [S₀, LinearMap.coe_mk, AddHom.coe_mk]
      rw [hσt, hUt, LinearEquiv.apply_symm_apply]
      simpa using add_sub_cancel (t • e0) v
    exact hmain
  · intro w
    show (S₀ w).ofLp 0 = σ w
    simp only [S₀, LinearMap.coe_mk, AddHom.coe_mk]
    rw [PiLp.add_apply, PiLp.smul_apply, he0, smul_eq_mul, mul_one, hθ0, add_zero]

/-- **Splitting a surjection with a prescribed coordinate.**  If `a : ℝ^{(m+1)+k} → ℝ^k` is
surjective and `s` is a functional which does not vanish identically on `ker a`, then `a` is the
first component of a linear equivalence `ℝ^{(m+1)+k} ≃ ℝ^k × ℝ^{m+1}` whose second component has
zeroth coordinate equal to `s` on `ker a`. -/
theorem exists_linearEquiv_prod_coord (m k : ℕ)
    (a : EuclideanSpace ℝ (Fin ((m + k) + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (ha : Function.Surjective a)
    (s : EuclideanSpace ℝ (Fin ((m + k) + 1)) →L[ℝ] ℝ)
    (hs : ∃ v, a v = 0 ∧ s v ≠ 0) :
    ∃ T : EuclideanSpace ℝ (Fin ((m + k) + 1)) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (m + 1))),
      (∀ v, (T v).1 = a v) ∧ (∀ v, a v = 0 → (T v).2 0 = s v) := by
  obtain ⟨T₁, hT₁⟩ := exists_linearEquiv_prod_ker m k a ha
  have hW : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+1))) = m + 1 := by
    rw [finrank_euclideanSpace]; simp
  let T₁' : EuclideanSpace ℝ (Fin ((m+k)+1)) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (m+1))) := T₁.toLinearEquiv
  have hT₁' : ∀ v, (T₁' v).1 = a v := fun v => hT₁ v
  -- the induced functional on the second factor
  let σ₁ : EuclideanSpace ℝ (Fin (m+1)) →ₗ[ℝ] ℝ :=
    (s : EuclideanSpace ℝ (Fin ((m+k)+1)) →ₗ[ℝ] ℝ).comp
      (T₁'.symm.comp (LinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin (m+1)))))
  have hσ₁ : σ₁ ≠ 0 := by
    obtain ⟨v, hv, hsv⟩ := hs
    intro h0
    have hp : ((0 : EuclideanSpace ℝ (Fin k)), (T₁' v).2) = T₁' v := by
      rw [Prod.ext_iff]
      exact ⟨by rw [hT₁' v, hv], rfl⟩
    have hsym : T₁'.symm ((0 : EuclideanSpace ℝ (Fin k)), (T₁' v).2) = v := by
      rw [hp, LinearEquiv.symm_apply_apply]
    have hzero : σ₁ (T₁' v).2 = 0 := by rw [h0]; rfl
    have hzero' : s (T₁'.symm ((0 : EuclideanSpace ℝ (Fin k)), (T₁' v).2)) = 0 := by
      simpa [σ₁] using hzero
    rw [hsym] at hzero'
    exact hsv hzero'
  obtain ⟨S, hS⟩ := exists_linearEquiv_coord' (n := m) σ₁ hσ₁ hW
  refine ⟨(T₁'.trans ((LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin k))).prodCongr
    S)).toContinuousLinearEquiv, ?_, ?_⟩
  · intro v
    change (T₁' v).1 = a v
    exact hT₁' v
  · intro v hv
    change (S (T₁' v).2) 0 = s v
    rw [hS]
    have hp : ((0 : EuclideanSpace ℝ (Fin k)), (T₁' v).2) = T₁' v := by
      rw [Prod.ext_iff]
      exact ⟨by rw [hT₁' v, hv], rfl⟩
    have hsym : T₁'.symm ((0 : EuclideanSpace ℝ (Fin k)), (T₁' v).2) = v := by
      rw [hp, LinearEquiv.symm_apply_apply]
    show s (T₁'.symm ((0 : EuclideanSpace ℝ (Fin k)), (T₁' v).2)) = s v
    rw [hsym]

end

end Work.ThomBordism.Transversality.Preimage
