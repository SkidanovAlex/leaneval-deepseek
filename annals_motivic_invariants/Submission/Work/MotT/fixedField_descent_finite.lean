import Mathlib

set_option linter.unusedVariables false -- v435-speed

set_option linter.style.haveILetI false

namespace Work.MotT

/-- **Artin/Speiser descent for a finite group of `𝕜`-automorphisms** (the generalisation of
`Work.MotC.fixedField_descent`, which is the case of a cyclic group of order 5).  Declare it in
namespace `Work.MotT`.

Let `𝕜 ⊆ L ⊆ M` be a tower of fields, `H` a finite group of `𝕜`-automorphisms of `L` whose fixed
field is exactly `𝕜`, and `ρ : H →* Aut_𝕜(M)` a group homomorphism whose action on the image of `L`
in `M` is the action of `H` on `L` (`hρ`) — so that `ρ` is automatically injective.  Then the fixed
field `Φ = M^{ρ(H)}` of the action is linearly disjoint from `L` over `𝕜`, and `Φ` together with `L`
generates `M`.

Route.  Artin (`FixedPoints.finrank_eq_card`) gives `[M : Φ] = |ρ.range| = |H|`, and `hfix`
together with Artin on `L` gives `[L : 𝕜] = |H|`.  An element of `Φ ⊓ L` is fixed by all of `H`,
hence lies in `𝕜`, so `Φ ⊓ L' = ⊥` for `L' := (IsScalarTower.toAlgHom 𝕜 L M).fieldRange`.  Then
`Φ ⊔ L' = ⊤` and `Φ.LinearDisjoint L` follow exactly as in `Work.MotC.fixedField_descent`: identify
`M` with the `Φ`-span of `L'` (a `𝕜`-basis of `L` has `|H| = [M : Φ]` elements), `Φ` is a field so
a finite-dimensional domain over it is a field, giving `⊤ ≤ Submodule.span Φ L'`, and then
`linearIndependent_of_top_le_span_of_card_eq_finrank` gives the linear independence of the basis over
`Φ`, which is `Φ.LinearDisjoint L` via `IntermediateField.LinearDisjoint.of_basis_right'`.  Use the
`Work.MotC.fixedField_descent` file as a template; the only genuinely new ingredient is that the
group need not be cyclic, so the "prime degree" step of that proof is replaced by the tower law
(together with `[L : Φ ⊓ L'] = [L : 𝕜] = [M : Φ]`, i.e. the compositum degree formula
`Module.finrank ↥A ↥(A ⊔ B) = Module.finrank ↥(A ⊓ B) ↥B` for finite `B/(A ⊓ B)`, which may be
proved by hand — or else apply Artin's finrank formula again on `Φ ⊔ L'`, whose fixed field under the
restricted action is `Φ`). -/
theorem fixedField_descent_finite {𝕜 L M : Type*} [Field 𝕜] [Field L] [Field M]
    [Algebra 𝕜 L] [Algebra L M] [Algebra 𝕜 M] [IsScalarTower 𝕜 L M]
    (H : Subgroup (L ≃ₐ[𝕜] L)) [Fintype H]
    (hfix : ∀ l : L, (∀ h : H, (h : L ≃ₐ[𝕜] L) l = l) → ∃ c : 𝕜, algebraMap 𝕜 L c = l)
    (ρ : H →* (M ≃ₐ[𝕜] M))
    (hρ : ∀ (h : H) (l : L), ρ h (algebraMap L M l) = algebraMap L M ((h : L ≃ₐ[𝕜] L) l)) :
    (IntermediateField.fixedField (ρ.range)).LinearDisjoint L ∧
      IntermediateField.fixedField (ρ.range) ⊔
        (IsScalarTower.toAlgHom 𝕜 L M).fieldRange = ⊤ := by
  classical
  set F : IntermediateField 𝕜 M := IntermediateField.fixedField (ρ.range) with hFdef
  set fL : L →ₐ[𝕜] M := IsScalarTower.toAlgHom 𝕜 L M with hfL
  set L' : IntermediateField 𝕜 M := fL.fieldRange with hL'def
  set E : IntermediateField 𝕜 M := F ⊔ L' with hEdef
  have hfLapply : ∀ l : L, fL l = algebraMap L M l := fun l => by rw [hfL]; rfl
  have hL'E : L' ≤ E := by rw [hEdef]; exact le_sup_right
  have hFE : F ≤ E := by rw [hEdef]; exact le_sup_left
  have hmemE : ∀ l : L, fL l ∈ E := fun l => hL'E (AlgHom.mem_fieldRange.mpr ⟨l, rfl⟩)
  -- ## `ρ` is injective
  have hinj : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    apply AlgEquiv.ext
    intro l
    have h1 : ρ a (algebraMap L M l) = ρ b (algebraMap L M l) := by rw [hab]
    rw [hρ a l, hρ b l] at h1
    exact (algebraMap L M).injective h1
  haveI hRangeFin : Fintype ↥(ρ.range) := Fintype.ofEquiv H (MonoidHom.ofInjective hinj)
  have hcardρ : Fintype.card ↥(ρ.range) = Fintype.card H := by
    rw [← Fintype.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  -- ## Artin on `M`
  have hfinF : Module.finrank ↥F M = Fintype.card H := by
    have h : Module.finrank ↥(IntermediateField.fixedField (ρ.range)) M =
        Fintype.card ↥(ρ.range) := FixedPoints.finrank_eq_card ↥(ρ.range) M
    rw [← hFdef, hcardρ] at h
    exact h
  haveI hMFd : FiniteDimensional ↥F M :=
    Module.finite_of_finrank_pos (by rw [hfinF]; exact Fintype.card_pos)
  -- ## `hfix` says the fixed field of `H` on `L` is `𝕜`
  have hFBot : IntermediateField.fixedField H = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨c, hc⟩ := hfix x (fun h => (IntermediateField.mem_fixedField_iff H x).mp hx h h.2)
    rw [IntermediateField.mem_bot]
    exact ⟨c, hc⟩
  have hfinL : Module.finrank 𝕜 L = Fintype.card H := by
    have h : Module.finrank ↥(IntermediateField.fixedField H) L = Fintype.card H :=
      FixedPoints.finrank_eq_card H L
    rw [hFBot] at h
    rw [← h, ← Module.finrank_mul_finrank 𝕜 ↥(⊥ : IntermediateField 𝕜 L) L,
      IntermediateField.finrank_bot, one_mul]
  -- ## stability of `E` under `ρ(H)`
  have hFstab : ∀ g : ↥(ρ.range), F.map (g : M ≃ₐ[𝕜] M).toAlgHom ≤ F := by
    intro g z hz
    rw [hFdef] at hz ⊢
    rw [IntermediateField.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hgy : (g : M ≃ₐ[𝕜] M) y = y :=
      (IntermediateField.mem_fixedField_iff (ρ.range) y).mp hy g g.2
    change (g : M ≃ₐ[𝕜] M) y ∈ IntermediateField.fixedField (ρ.range)
    rw [hgy]
    exact hy
  have hL'stab : ∀ g : ↥(ρ.range), L'.map (g : M ≃ₐ[𝕜] M).toAlgHom ≤ L' := by
    intro g z hz
    rw [hL'def] at hz ⊢
    rw [IntermediateField.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨l, hl⟩ := AlgHom.mem_fieldRange.mp hy
    rw [← hl]
    obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp g.2
    rw [← hh]
    refine AlgHom.mem_fieldRange.mpr ⟨(h : L ≃ₐ[𝕜] L) l, ?_⟩
    rw [hfLapply, hfLapply]
    exact (hρ h l).symm
  have hstab : ∀ g : ↥(ρ.range), E.map (g : M ≃ₐ[𝕜] M).toAlgHom ≤ E := by
    intro g
    rw [hEdef, IntermediateField.map_sup]
    exact sup_le (le_trans (hFstab g) le_sup_left) (le_trans (hL'stab g) le_sup_right)
  haveI hLfd : FiniteDimensional 𝕜 L :=
    Module.finite_of_finrank_pos (by rw [hfinL]; exact Fintype.card_pos)
  -- ## a `𝕜`-basis of `L` with `|H|` elements
  set hbasis : Module.Basis (Fin (Fintype.card H)) 𝕜 L :=
    (Module.finBasis 𝕜 L).reindex (finCongr hfinL) with hbasisdef
  -- ## `E` viewed as an intermediate field of `M / F`
  let EF : IntermediateField ↥F M := IntermediateField.extendScalars hFE
  let hinc : ↥EF →ₗ[↥F] M :=
    { toFun := fun x => x.val
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hincinj : Function.Injective hinc := fun x y h => Subtype.ext h
  -- ## the restriction of `ρ(H)` to `E` as a family of `F`-algebra maps
  let PSI : ↥(ρ.range) → (↥EF →ₐ[↥F] ↥EF) := fun g => {
    toFun := fun x => ⟨(g : M ≃ₐ[𝕜] M) x.val, hstab g (by
      rw [IntermediateField.mem_map]
      exact ⟨x.val, x.property, rfl⟩)⟩
    map_one' := by ext; simp
    map_mul' := by intro a b; ext; simp
    map_zero' := by ext; simp
    map_add' := by intro a b; ext; simp
    commutes' := by
      intro a
      ext
      have haF : (algebraMap ↥F ↥EF a).val ∈ F := by
        rw [show (algebraMap ↥F ↥EF a).val = (a : M) from rfl]
        exact a.2
      have hfixa := (IntermediateField.mem_fixedField_iff (ρ.range) (algebraMap ↥F ↥EF a).val).mp
        (by rw [← hFdef]; exact haF) (g : M ≃ₐ[𝕜] M) g.2
      show (g : M ≃ₐ[𝕜] M) (algebraMap ↥F ↥EF a).val = (algebraMap ↥F ↥EF a).val
      exact hfixa }
  have hPSIinj : Function.Injective PSI := by
    intro g₁ g₂ hg
    obtain ⟨h₁, hh₁⟩ := MonoidHom.mem_range.mp g₁.property
    obtain ⟨h₂, hh₂⟩ := MonoidHom.mem_range.mp g₂.property
    have hval : ∀ x : ↥EF, (g₁ : M ≃ₐ[𝕜] M) x.val = (g₂ : M ≃ₐ[𝕜] M) x.val := fun x =>
      congrArg Subtype.val (DFunLike.congr_fun hg x)
    have hh : h₁ = h₂ := by
      apply Subtype.ext
      apply AlgEquiv.ext
      intro l
      have h1 := hval ⟨fL l, hmemE l⟩
      rw [← hh₁, ← hh₂] at h1
      change ρ h₁ (algebraMap L M l) = ρ h₂ (algebraMap L M l) at h1
      rw [hρ h₁ l, hρ h₂ l] at h1
      exact (algebraMap L M).injective h1
    apply Subtype.ext
    rw [← hh₁, ← hh₂, hh]
  -- ## `|H| ≤ [E : F]`
  have h_le : Fintype.card H ≤ Module.finrank ↥F ↥EF := by
    have h1 : Fintype.card ↥(ρ.range) ≤ Fintype.card (↥EF →ₐ[↥F] ↥EF) :=
      Fintype.card_le_of_injective PSI hPSIinj
    have h2 : Fintype.card (↥EF →ₐ[↥F] ↥EF) ≤ Module.finrank ↥F ↥EF := AlgHom.card_le
    calc Fintype.card H = Fintype.card ↥(ρ.range) := hcardρ.symm
      _ ≤ Fintype.card (↥EF →ₐ[↥F] ↥EF) := h1
      _ ≤ Module.finrank ↥F ↥EF := h2
  -- ## `[E : F] ≤ |H|`
  have h_ge : Module.finrank ↥F ↥EF ≤ Fintype.card H := by
    have h1 : Module.finrank ↥F ↥EF ≤ Module.finrank ↥F M :=
      LinearMap.finrank_le_finrank_of_injective hincinj
    rw [hfinF] at h1
    exact h1
  have hfinE : Module.finrank ↥F ↥EF = Fintype.card H := le_antisymm h_ge h_le
  -- ## tower law: `[M : E] = 1`
  have htower : Module.finrank ↥F ↥EF * Module.finrank ↥E M = Module.finrank ↥F M :=
    Module.finrank_mul_finrank ↥F ↥EF M
  rw [hfinE, hfinF] at htower
  have hEfin : Module.finrank ↥E M = 1 :=
    Nat.eq_of_mul_eq_mul_left Fintype.card_pos (by rw [mul_one]; exact htower)
  have hEtop : E = ⊤ := IntermediateField.finrank_eq_one_iff_eq_top.mp hEfin
  -- ## the `F`-span of `L'` is everything
  set W : Submodule ↥F M := Submodule.span ↥F (L' : Set M) with hWdef
  have hmul : W * W ≤ W := by
    rw [hWdef, Submodule.span_mul_span]
    refine Submodule.span_mono ?_
    rintro x ⟨y, hy, z, hz, rfl⟩
    exact L'.mul_mem hy hz
  have hone : (1 : M) ∈ W := Submodule.subset_span L'.one_mem
  have hFmem : ∀ g : ↥F, (g : M) ∈ W := by
    intro g
    have h1 : (g : M) = g • (1 : M) := (mul_one _).symm
    rw [h1]
    exact Submodule.smul_mem W g hone
  let S : Subalgebra ↥F M :=
    { carrier := (W : Set M)
      mul_mem' := fun ha hb => hmul (Submodule.mul_mem_mul ha hb)
      one_mem' := hone
      add_mem' := fun ha hb => W.add_mem ha hb
      zero_mem' := W.zero_mem
      algebraMap_mem' := fun r => hFmem r }
  haveI hSdom : IsDomain ↥S := inferInstance
  haveI hSfin : FiniteDimensional ↥F ↥S := inferInstanceAs (FiniteDimensional ↥F ↥W)
  have hfield : IsField ↥S := IsField.of_isDomain_of_finite ↥F ↥S
  let Wif' : IntermediateField ↥F M := S.toIntermediateField' hfield
  let Wif : IntermediateField 𝕜 M :=
    Wif'.toSubfield.toIntermediateField (fun a => by
      rw [IsScalarTower.algebraMap_apply 𝕜 ↥F M]
      exact Wif'.algebraMap_mem _)
  have hWifcoe : (Wif : Set M) = (W : Set M) := rfl
  have hFW : F ≤ Wif := by
    intro x hx
    change x ∈ (Wif : Set M)
    rw [hWifcoe]
    exact hFmem ⟨x, hx⟩
  have hLW : L' ≤ Wif := by
    intro x hx
    change x ∈ (Wif : Set M)
    rw [hWifcoe]
    exact Submodule.subset_span hx
  have hle : F ⊔ L' ≤ Wif := sup_le hFW hLW
  rw [← hEdef, hEtop] at hle
  have hWtop : (⊤ : Submodule ↥F M) ≤ W := by
    intro x hx
    have hx' : x ∈ Wif := hle trivial
    change x ∈ (Wif : Set M) at hx'
    rw [hWifcoe] at hx'
    exact hx'
  -- ## linear disjointness
  set W₂ : Submodule ↥F M :=
    Submodule.span ↥F (Set.range (fun i : Fin (Fintype.card H) => fL (hbasis i))) with hW₂
  have hsub : (L' : Set M) ⊆ (W₂ : Set M) := by
    intro x hx
    have hx' : x ∈ fL.fieldRange := by rw [← hL'def]; exact hx
    obtain ⟨l, rfl⟩ := AlgHom.mem_fieldRange.mp hx'
    show fL l ∈ (W₂ : Set M)
    rw [← hbasis.sum_repr l, map_sum]
    refine Submodule.sum_mem W₂ (fun i _ => ?_)
    rw [map_smul]
    have hmem : (⟨algebraMap 𝕜 M (hbasis.repr l i), F.algebraMap_mem _⟩ : ↥F) • fL (hbasis i)
        ∈ W₂ := Submodule.smul_mem W₂ _ (Submodule.subset_span ⟨i, rfl⟩)
    simpa using hmem
  have hspan2 : (⊤ : Submodule ↥F M) ≤ W₂ := le_trans hWtop (Submodule.span_le.mpr hsub)
  have hli : LinearIndependent ↥F (fun i : Fin (Fintype.card H) => fL (hbasis i)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan2
      (by rw [Fintype.card_fin, hfinF])
  exact ⟨IntermediateField.LinearDisjoint.of_basis_right' (A := F) (b := hbasis) hli, hEtop⟩

end Work.MotT
