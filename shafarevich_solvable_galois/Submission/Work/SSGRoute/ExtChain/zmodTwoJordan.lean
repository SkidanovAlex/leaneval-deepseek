import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Jordan normal form of an involution of a finite `𝔽₂`-vector space

Let `V` be a finite `𝔽₂`-vector space and `S : V ≃ₗ[𝔽₂] V` an involution (`S * S = 1`).  Put
`ε = S - 1`, so that `ε² = 0`.  Then `S` fixes `ker ε` and shifts `im ε ⊆ ker ε`:

* `U` a complement of `K = ker ε`,
* `ε` maps `U` isomorphically onto `I = im ε`,
* `W` a complement of `I` inside `K`,

give a direct sum decomposition `V = U ⊕ I ⊕ W` on which `S = 1 + ε` acts by
`(u, i, w) ↦ (u, i + ε u, w)`.  In the coordinates `x = u` (a basis of `U`), `y = ε u` (the
corresponding basis of `I`), `w` (a basis of `W`), the action of `S` becomes

    `(x, (w, y)) ↦ (x, (w, x + y))`,

which is the Jordan/transvection normal form used in the structure theory of finite `𝔽₂[C₂]`-modules.
-/

namespace Work.SSGRoute.ExtChain

noncomputable section

attribute [local instance] Classical.decEq

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

/-- In a `ZMod 2`-module, `x + x = 0`. -/
theorem zmod_two_add_self (x : V) : x + x = 0 := by
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  have h : (2 : ℕ) • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 x, h2, zero_smul]
  rwa [two_nsmul] at h

section Jordan

variable [Finite V]

/-- **Jordan normal form of an involution of a finite `𝔽₂`-vector space.**  There are `a, b` and a
linear equivalence `e` such that `S (e t) = e (t.1, (t.2.1, t.1 + t.2.2))`: `b` blocks of the
2-dimensional transvection `(x, y) ↦ (x, x + y)` and `a` fixed coordinates. -/
theorem zmod_two_jordan (S : V ≃ₗ[ZMod 2] V) (hS : S * S = 1) :
    ∃ (a b : ℕ) (e : ((Fin b → ZMod 2) × ((Fin a → ZMod 2) × (Fin b → ZMod 2))) ≃ₗ[ZMod 2] V),
      ∀ t : (Fin b → ZMod 2) × ((Fin a → ZMod 2) × (Fin b → ZMod 2)),
        S (e t) = e (t.1, (t.2.1, t.1 + t.2.2)) := by
  classical
  -- `S` is an involution
  have hSS : ∀ v : V, S (S v) = v := fun v => by
    have h := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hS
    rw [LinearEquiv.mul_eq_trans, LinearEquiv.trans_apply] at h
    simpa using h
  -- `ε = S - 1`
  let ε : V →ₗ[ZMod 2] V :=
    { toFun := fun v => S v - v
      map_add' := fun x y => by
        show S (x + y) - (x + y) = (S x - x) + (S y - y)
        rw [map_add]
        abel
      map_smul' := fun c x => by
        show S (c • x) - c • x = c • (S x - x)
        rw [map_smul, smul_sub] }
  have hε_apply : ∀ v : V, ε v = S v - v := fun _ => rfl
  have hεε : ∀ v : V, ε (ε v) = 0 := fun v => by
    rw [hε_apply, hε_apply, map_sub, hSS v]
    rw [show (v - S v) - (S v - v) = (v - S v) + (v - S v) from by abel,
      zmod_two_add_self]
  -- kernel and range of `ε`
  let K : Submodule (ZMod 2) V := LinearMap.ker ε
  let I : Submodule (ZMod 2) V := LinearMap.range ε
  have hεK : ∀ x ∈ K, ε x = 0 := fun x hx => hx
  have hIK : I ≤ K := fun x hx => by
    obtain ⟨y, hy⟩ := (LinearMap.mem_range).mp hx
    rw [← hy]
    exact hεε y
  have hIrange : ∀ x, x ∈ I ↔ ∃ y, ε y = x := fun x => LinearMap.mem_range
  -- complements
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl K
  -- `I' = I ∩ K` as a submodule of `K`, and `W'` a complement of it in `K`
  let I' : Submodule (ZMod 2) K := I.comap K.subtype
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl I'
  let W : Submodule (ZMod 2) V := W'.map K.subtype
  have hWK : W ≤ K := fun x hx => by
    obtain ⟨y, _, rfl⟩ := (Submodule.mem_map).mp hx
    exact y.2
  have hWI : W ⊔ I = K := by
    refine le_antisymm (sup_le hWK hIK) ?_
    intro x hx
    have hmem : (⟨x, hx⟩ : K) ∈ I' ⊔ W' := by rw [hW'.sup_eq_top]; trivial
    rw [Submodule.mem_sup] at hmem
    obtain ⟨p, hp, q, hq, hpq⟩ := hmem
    rw [Submodule.mem_sup]
    refine ⟨(q : V), ?_, (p : V), hp, ?_⟩
    · exact Submodule.mem_map.mpr ⟨q, hq, rfl⟩
    · have hab' : (p : V) + (q : V) = x := congrArg Subtype.val hpq
      rw [add_comm]
      exact hab'
  have hWIdisj : W ⊓ I = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxI⟩ := hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_map).mp hxW
    have hyI' : y ∈ I' := hxI
    have : y ∈ I' ⊓ W' := ⟨hyI', hy⟩
    rw [hW'.inf_eq_bot, Submodule.mem_bot] at this
    rw [this]
    rfl
  -- injectivity of `ε` on `U` and surjectivity onto `I`
  have hεUinj : ∀ u ∈ U, ε u = 0 → u = 0 := fun u hu h0 => by
    have hmem : u ∈ U ⊓ K := ⟨hu, h0⟩
    rw [inf_comm, hU.inf_eq_bot, Submodule.mem_bot] at hmem
    exact hmem
  have hεUsurj : ∀ x ∈ I, ∃ u ∈ U, ε u = x := fun x hx => by
    obtain ⟨y, hy⟩ := (LinearMap.mem_range).mp hx
    have hymem : y ∈ K ⊔ U := by rw [hU.sup_eq_top]; trivial
    rw [Submodule.mem_sup] at hymem
    obtain ⟨k, hkK, u, huU, hku⟩ := hymem
    refine ⟨u, huU, ?_⟩
    rw [← hy, ← hku, map_add, hεK k hkK, zero_add]
  -- bases
  let b := Module.finrank (ZMod 2) U
  let a := Module.finrank (ZMod 2) W
  haveI : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  let cU : U ≃ₗ[ZMod 2] (Fin b → ZMod 2) :=
    (Module.finBasis (ZMod 2) U).repr.trans
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Fin b))
  let cW : W ≃ₗ[ZMod 2] (Fin a → ZMod 2) :=
    (Module.finBasis (ZMod 2) W).repr.trans
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Fin a))
  -- the explicit linear map
  let F : ((Fin b → ZMod 2) × ((Fin a → ZMod 2) × (Fin b → ZMod 2))) →ₗ[ZMod 2] V :=
    { toFun := fun t => (cU.symm t.1 : V) + (cW.symm t.2.1 : V) + ε (cU.symm t.2.2 : V)
      map_add' := fun t t' => by
        show (cU.symm (t + t').1 : V) + (cW.symm (t + t').2.1 : V) + ε (cU.symm (t + t').2.2 : V)
          = ((cU.symm t.1 : V) + (cW.symm t.2.1 : V) + ε (cU.symm t.2.2 : V))
            + ((cU.symm t'.1 : V) + (cW.symm t'.2.1 : V) + ε (cU.symm t'.2.2 : V))
        simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]
        abel
      map_smul' := fun c t => by
        show (cU.symm (c • t).1 : V) + (cW.symm (c • t).2.1 : V) + ε (cU.symm (c • t).2.2 : V)
          = c • ((cU.symm t.1 : V) + (cW.symm t.2.1 : V) + ε (cU.symm t.2.2 : V))
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, Submodule.coe_smul] }
  have hF_apply : ∀ t : (Fin b → ZMod 2) × ((Fin a → ZMod 2) × (Fin b → ZMod 2)),
      F t = (cU.symm t.1 : V) + (cW.symm t.2.1 : V) + ε (cU.symm t.2.2 : V) := fun _ => rfl
  -- injectivity of `F`
  have hFinj : Function.Injective F := by
    have hker : ∀ t, F t = 0 → t = 0 := by
      intro t ht
      rw [hF_apply t] at ht
      have ht' : (cU.symm t.1 : V) + ((cW.symm t.2.1 : V) + ε (cU.symm t.2.2 : V)) = 0 := by
        rw [← ht]
        abel
      have huK : (cU.symm t.1 : V) ∈ K := by
        have hx : (cU.symm t.1 : V) = -((cW.symm t.2.1 : V) + ε (cU.symm t.2.2 : V)) :=
          eq_neg_iff_add_eq_zero.mpr ht'
        rw [hx]
        exact K.neg_mem (K.add_mem (hWK (cW.symm t.2.1).2)
          (hIK ((LinearMap.mem_range).mpr ⟨_, rfl⟩)))
      have hx0 : (cU.symm t.1 : V) = 0 := by
        have hmem : (cU.symm t.1 : V) ∈ K ⊓ U := ⟨huK, (cU.symm t.1).2⟩
        rw [hU.inf_eq_bot, Submodule.mem_bot] at hmem
        exact hmem
      have h1 : t.1 = 0 := by
        have hsub : cU.symm t.1 = 0 := Subtype.ext (by simpa using hx0)
        have hc : cU (cU.symm t.1) = 0 := by rw [hsub, map_zero]
        rwa [cU.apply_symm_apply] at hc
      have ht2 : (cW.symm t.2.1 : V) + ε (cU.symm t.2.2 : V) = 0 := by
        have hcoe : (cU.symm t.1 : V) = 0 := by simp [h1]
        rw [hcoe, zero_add] at ht'
        exact ht'
      have hwI : (cW.symm t.2.1 : V) ∈ I := by
        have hx : (cW.symm t.2.1 : V) = -(ε (cU.symm t.2.2 : V)) :=
          eq_neg_iff_add_eq_zero.mpr ht2
        rw [hx]
        exact I.neg_mem ((LinearMap.mem_range).mpr ⟨_, rfl⟩)
      have hw0 : (cW.symm t.2.1 : V) = 0 := by
        have hmem : (cW.symm t.2.1 : V) ∈ W ⊓ I := ⟨(cW.symm t.2.1).2, hwI⟩
        rw [hWIdisj, Submodule.mem_bot] at hmem
        exact hmem
      have h3 : t.2.1 = 0 := by
        have hsub : cW.symm t.2.1 = 0 := Subtype.ext (by simpa using hw0)
        have hc : cW (cW.symm t.2.1) = 0 := by rw [hsub, map_zero]
        rwa [cW.apply_symm_apply] at hc
      have hi0 : ε (cU.symm t.2.2 : V) = 0 := by
        have hcoe : (cW.symm t.2.1 : V) = 0 := by simp [h3]
        rw [hcoe, zero_add] at ht2
        exact ht2
      have hy0 : (cU.symm t.2.2 : V) = 0 := by
        have hmem : (cU.symm t.2.2 : V) ∈ U ⊓ K := ⟨(cU.symm t.2.2).2, hi0⟩
        rw [inf_comm, hU.inf_eq_bot, Submodule.mem_bot] at hmem
        exact hmem
      have h5 : t.2.2 = 0 := by
        have hsub : cU.symm t.2.2 = 0 := Subtype.ext (by simpa using hy0)
        have hc : cU (cU.symm t.2.2) = 0 := by rw [hsub, map_zero]
        rwa [cU.apply_symm_apply] at hc
      exact Prod.ext h1 (Prod.ext h3 h5)
    intro p q hpq
    have hzero : F (p - q) = 0 := by rw [map_sub, hpq, sub_self]
    have := hker (p - q) hzero
    exact sub_eq_zero.mp this
  -- surjectivity of `F`
  have hFsurj : Function.Surjective F := by
    intro v
    have hv : v ∈ K ⊔ U := by rw [hU.sup_eq_top]; trivial
    rw [Submodule.mem_sup] at hv
    obtain ⟨k, hkK, u, huU, hku⟩ := hv
    have hk : k ∈ I ⊔ W := by rw [sup_comm, hWI]; exact hkK
    rw [Submodule.mem_sup] at hk
    obtain ⟨i, hiI, w, hwW, hiw⟩ := hk
    obtain ⟨u', hu'⟩ := (LinearMap.mem_range).mp hiI
    obtain ⟨u'', hu''U, hiu''⟩ := hεUsurj i hiI
    refine ⟨(cU ⟨u, huU⟩, (cW ⟨w, hwW⟩, cU ⟨u'', hu''U⟩)), ?_⟩
    rw [hF_apply]
    simp only [LinearEquiv.symm_apply_apply, Submodule.coe_mk, hiu'']
    rw [← hku, ← hiw]
    abel
  -- the equivariance
  have hSx : ∀ x : V, S x = x + ε x := fun x => by
    rw [hε_apply x]
    abel
  have heq : ∀ t : (Fin b → ZMod 2) × ((Fin a → ZMod 2) × (Fin b → ZMod 2)),
      S (F t) = F (t.1, (t.2.1, t.1 + t.2.2)) := by
    intro t
    have hw : ε (cW.symm t.2.1 : V) = 0 := hεK _ (hWK (cW.symm t.2.1).2)
    have hεF : ε (F t) = ε (cU.symm t.1 : V) := by
      rw [hF_apply t, map_add, map_add, hw, hεε]
      abel
    have hshift : F (t.1, (t.2.1, t.1 + t.2.2))
        = (cU.symm t.1 : V) + (cW.symm t.2.1 : V) + ε (cU.symm t.1 : V)
          + ε (cU.symm t.2.2 : V) := by
      rw [hF_apply]
      simp only [map_add, Submodule.coe_add]
      abel
    rw [hSx, hεF, hF_apply t, hshift]
    abel
  refine ⟨a, b, LinearEquiv.ofBijective F (show Function.Bijective F from ⟨hFinj, hFsurj⟩), ?_⟩
  intro t
  change S (F t) = F (t.1, (t.2.1, t.1 + t.2.2))
  exact heq t

end Jordan

end

end Work.SSGRoute.ExtChain
