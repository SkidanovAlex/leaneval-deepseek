import Mathlib
import Submission.Work.HallHigman.GLCore.Defs
import Submission.Work.HallHigman.eq_one_of_pow_eq_one_of_sq_sub_one_eq_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# L14 of the GL-core design: restriction / quotient inheritance

This file proves `Work.HallHigman.GLCore.restrict_or_quotient_of_coreHyp`, Step 2 of the proof
of Hall--Higman B (see `NOTES_LEAD_ft_hallhigman.md` §2.2).

Given the GL-core hypotheses `CoreHyp p Q X` on `V`, an invariant submodule `U`, and the failure
hypothesis `(X - 1) ^ (p - 1) = 0`, a counterexample is inherited either by the restriction to `U`
or by the quotient `V ⧸ U`.

The plumbing is as follows.  `stab U` is the subgroup of `GL(V) = (End K V)ˣ` consisting of the
units preserving `U` (together with their inverse); `restrUnit`/`restrHom` and
`quotUnit`/`quotHom` are the induced representations on `U` and `V ⧸ U`.  The key point is that
`CoreHyp` is preserved by any monoid homomorphism with a non-commuting image
(`coreHyp_map`), while the failure hypothesis is inherited by the restriction
(`restrUnit_sub_one_pow_eq_zero`) and by the quotient (`quotUnit_sub_one_pow_eq_zero`).
If on both `U` and `V ⧸ U` the image of `X` commuted with the image of `Q`, the commutator
`c = X a X⁻¹ a⁻¹` would act as the identity on `U` and on `V ⧸ U`, hence `(c - 1)² = 0`
(`sq_sub_one_eq_zero_of_restr_eq_one_of_quot_eq_one`), and since `p ∤ |Q|` we get `c = 1`,
contradiction.
-/

namespace Work.HallHigman.GLCore

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The subgroup of `GL(V) = (End K V)ˣ` of units which preserve the submodule `U` together with
their inverse. -/
noncomputable def stab (U : Submodule K V) : Subgroup (Module.End K V)ˣ where
  carrier := {a | U ≤ U.comap ((a : (Module.End K V)ˣ) : Module.End K V) ∧
                  U ≤ U.comap ((((a : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V))}
  mul_mem' := by
    intro a b ha hb
    exact ⟨fun x hx => ha.1 (hb.1 hx), fun x hx => hb.2 (ha.2 hx)⟩
  one_mem' := by
    constructor <;> intro x hx <;> simpa using hx
  inv_mem' := by
    intro x hx
    exact ⟨hx.2, by simpa using hx.1⟩

/-- Restriction of a stabilising unit of `GL(V)` to the invariant submodule `U`, as a unit of
`End K U`. -/
noncomputable def restrUnit (U : Submodule K V) (a : stab U) : (Module.End K U)ˣ :=
  let r : Module.End K U :=
    ((a : (Module.End K V)ˣ) : Module.End K V).restrict (fun v hv => (a.2).1 hv)
  let r' : Module.End K U :=
    ((((a : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ)) : Module.End K V).restrict
      (fun v hv => (a.2).2 hv)
  Units.mk r r'
    (by ext x; rw [Module.End.mul_apply]; simp only [r, r', LinearMap.restrict_apply];
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl)
    (by ext x; rw [Module.End.mul_apply]; simp only [r, r', LinearMap.restrict_apply];
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]; rfl)

/-- The action of a stabilising unit of `GL(V)` on the quotient `V ⧸ U`, as a unit of
`End K (V ⧸ U)`. -/
noncomputable def quotUnit (U : Submodule K V) (a : stab U) : (Module.End K (V ⧸ U))ˣ :=
  let q : Module.End K (V ⧸ U) :=
    Submodule.mapQ U U (((a : (Module.End K V)ˣ) : Module.End K V)) (a.2).1
  let q' : Module.End K (V ⧸ U) :=
    Submodule.mapQ U U ((((a : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ)) : Module.End K V) (a.2).2
  Units.mk q q'
    (by ext x; simp only [LinearMap.comp_apply, Module.End.mul_apply, q, q', Submodule.mapQ_apply,
        Submodule.mkQ_apply]
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl)
    (by ext x; simp only [LinearMap.comp_apply, Module.End.mul_apply, q, q', Submodule.mapQ_apply,
        Submodule.mkQ_apply]
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]; rfl)

/-- The restriction map `stab U →* (End K U)ˣ`. -/
noncomputable def restrHom (U : Submodule K V) : stab U →* (Module.End K U)ˣ where
  toFun := restrUnit U
  map_one' := by ext x; simp [restrUnit, LinearMap.restrict_apply]
  map_mul' := by intro a b; ext x; simp [restrUnit, LinearMap.restrict_apply, Module.End.mul_apply]

/-- The quotient map `stab U →* (End K (V ⧸ U))ˣ`. -/
noncomputable def quotHom (U : Submodule K V) : stab U →* (Module.End K (V ⧸ U))ˣ where
  toFun := quotUnit U
  map_one' := by ext x; simp [quotUnit, Submodule.mapQ_apply]
  map_mul' := by intro a b; ext x; simp [quotUnit, Submodule.mapQ_apply, Module.End.mul_apply]

/-- A unit of finite order `p` whose `p`-th power is `1` and whose action preserves `U` preserves
`U` together with its inverse: `X⁻¹ = X ^ (p - 1)`. -/
lemma mem_stab_of_pow_eq_one {p : ℕ} (hp : 0 < p) {X : (Module.End K V)ˣ} (hXp : X ^ p = 1)
    {U : Submodule K V} (hXU : ∀ v ∈ U, (X : Module.End K V) v ∈ U) : X ∈ stab U := by
  refine ⟨fun v hv => hXU v hv, ?_⟩
  have hinv : X⁻¹ = X ^ (p - 1) := by
    have h : X * X ^ (p - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne'), hXp]
    exact (eq_inv_of_mul_eq_one_right h).symm
  intro v hv
  rw [hinv, Units.val_pow_eq_pow_val]
  exact Module.End.pow_apply_mem_of_forall_mem (p - 1) hXU v hv

/-- A subgroup all of whose elements preserve `U` lies in `stab U`. -/
lemma le_stab_of_forall_mapsTo {Q : Subgroup (Module.End K V)ˣ} {U : Submodule K V}
    (hQU : ∀ a ∈ Q, ∀ v ∈ U, (a : Module.End K V) v ∈ U) : Q ≤ stab U := by
  intro a ha
  exact ⟨fun v hv => hQU a ha v hv, fun v hv => hQU a⁻¹ (inv_mem ha) v hv⟩

/-- The linear map induced by `f - g` on the quotient is the difference of the induced maps. -/
lemma mapQ_sub (U : Submodule K V) (f g : Module.End K V) (hf : U ≤ U.comap f) (hg : U ≤ U.comap g)
    (hfg : U ≤ U.comap (f - g) := fun _ hx => U.sub_mem (hf hx) (hg hx)) :
    U.mapQ U (f - g) hfg = U.mapQ U f hf - U.mapQ U g hg := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  exact map_sub U.mkQ (f x) (g x)

/-- The failure hypothesis `(X - 1) ^ (p - 1) = 0` is inherited by the restriction to `U`. -/
lemma restrUnit_sub_one_pow_eq_zero {p : ℕ} {U : Submodule K V} {X : (Module.End K V)ˣ}
    (hX : X ∈ stab U) (hfail : ((X : Module.End K V) - 1) ^ (p - 1) = 0) :
    ((restrUnit U ⟨X, hX⟩ : Module.End K U) - 1) ^ (p - 1) = 0 := by
  refine Module.End.submodule_pow_eq_zero_of_pow_eq_zero (N := U)
    (g := (restrUnit U ⟨X, hX⟩ : Module.End K U) - 1) (G := ((X : Module.End K V) - 1)) ?_ hfail
  ext u
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
    restrUnit, LinearMap.restrict_apply, Submodule.coe_sub, Module.End.one_apply]

/-- The failure hypothesis `(X - 1) ^ (p - 1) = 0` is inherited by the quotient `V ⧸ U`. -/
lemma quotUnit_sub_one_pow_eq_zero {p : ℕ} {U : Submodule K V} {X : (Module.End K V)ˣ}
    (hX : X ∈ stab U) (hfail : ((X : Module.End K V) - 1) ^ (p - 1) = 0) :
    ((quotUnit U ⟨X, hX⟩ : Module.End K (V ⧸ U)) - 1) ^ (p - 1) = 0 := by
  have h1 : (1 : Module.End K (V ⧸ U)) = U.mapQ U (1 : Module.End K V)
      (le_of_eq (Submodule.comap_id U)) := (Submodule.mapQ_id U).symm
  have hsub : (quotUnit U ⟨X, hX⟩ : Module.End K (V ⧸ U)) - 1
      = U.mapQ U ((X : Module.End K V) - 1) (fun v hv =>
          show ((X : Module.End K V) - 1) v ∈ U from by
            simpa [LinearMap.sub_apply, Module.End.one_apply] using U.sub_mem (hX.1 hv) hv) := by
    rw [show (quotUnit U ⟨X, hX⟩ : Module.End K (V ⧸ U))
          = U.mapQ U ((X : Module.End K V)) hX.1 from rfl, h1]
    rw [← mapQ_sub]
  rw [hsub, ← Submodule.mapQ_pow]
  ext x
  simp only [LinearMap.comp_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  rw [hfail]
  simp

/-- `CoreHyp` is preserved by a monoid homomorphism whose image of `X` does not commute with the
image of `Q`. -/
lemma coreHyp_map {p : ℕ} {U : Submodule K V} {Q : Subgroup (Module.End K V)ˣ}
    {X : (Module.End K V)ˣ} (h : CoreHyp p Q X) (hQ : Q ≤ stab U) (hX : X ∈ stab U)
    {W : Type*} [AddCommGroup W] [Module K W] (f : stab U →* (Module.End K W)ˣ)
    (hnc : ∃ a ∈ (Q.subgroupOf (stab U)).map f, a * f ⟨X, hX⟩ ≠ f ⟨X, hX⟩ * a) :
    CoreHyp p ((Q.subgroupOf (stab U)).map f) (f ⟨X, hX⟩) := by
  haveI := h.finite
  let ψ : Q →* (Q.subgroupOf (stab U)).map f :=
    (f.subgroupMap (Q.subgroupOf (stab U))).comp
      { toFun := fun a => ⟨⟨a, hQ a.2⟩, a.2⟩
        map_one' := by ext; rfl
        map_mul' := by intro a b; ext; rfl }
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := f.subgroupMap_surjective (Q.subgroupOf (stab U)) y
    refine ⟨⟨(x : stab U).val, x.2⟩, ?_⟩
    rw [← hx]
    ext
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, hnc⟩
  · exact Finite.of_surjective ψ hψ
  · exact h.odd.of_dvd_nat (Subgroup.card_dvd_of_surjective (f := ψ) hψ)
  · exact fun hd => h.cop (hd.trans (Subgroup.card_dvd_of_surjective (f := ψ) hψ))
  · have hXp : (⟨X, hX⟩ : stab U) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      simpa using h.pow
    rw [← map_pow, hXp, map_one]
  · intro a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    refine Subgroup.mem_map.mpr ⟨⟨X, hX⟩ * y * ⟨X, hX⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have hy' : (y : (Module.End K V)ˣ) ∈ Q := Subgroup.mem_subgroupOf.mp hy
      have hh := h.norm (y : (Module.End K V)ˣ) hy'
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hh
    · rw [map_mul, map_mul, map_inv]

/-- An endomorphism which is the identity on `U` and on `V ⧸ U` is unipotent of index `2`. -/
lemma sq_sub_one_eq_zero_of_restr_eq_one_of_quot_eq_one {U : Submodule K V}
    {a : (Module.End K V)ˣ} (ha : a ∈ stab U)
    (hr : restrUnit U ⟨a, ha⟩ = 1) (hq : quotUnit U ⟨a, ha⟩ = 1) :
    ((a : Module.End K V) - 1) ^ 2 = 0 := by
  have h2 : ∀ v ∈ U, ((a : Module.End K V) - 1) v = 0 := by
    intro v hv
    have h := congr_arg (fun f : (Module.End K U)ˣ =>
      (((f : Module.End K U) ⟨v, hv⟩ : U) : V)) hr
    simp only [restrUnit, LinearMap.restrict_apply, Module.End.one_apply] at h
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact h
  have h1 : ∀ v : V, ((a : Module.End K V) - 1) v ∈ U := by
    intro v
    have h := congr_arg (fun f : (Module.End K (V ⧸ U))ˣ =>
      (f : Module.End K (V ⧸ U)) (Submodule.Quotient.mk v)) hq
    simp only [quotUnit, Submodule.mapQ_apply] at h
    have h' : (a : Module.End K V) v - v ∈ U := (Submodule.Quotient.eq U).mp h
    simpa [LinearMap.sub_apply, Module.End.one_apply] using h'
  ext v
  rw [pow_two, Module.End.mul_apply]
  exact h2 _ (h1 v)

/-- **L14 of the GL-core design** (Step 2 of the proof of Hall--Higman B, see
`NOTES_LEAD_ft_hallhigman.md` §2.2): if `V` is not irreducible for `𝒬 ∪ {X}` and `U` is a proper
nontrivial invariant subspace, then a counterexample to the GL-core (same `p`, with
`(X - 1) ^ (p - 1) = 0`) is inherited either by the restriction to `U` or by the action on
`V ⧸ U`.  (If `X` commuted with the image of `𝒬` on both `U` and `V ⧸ U`, then for every `a ∈ 𝒬`
the commutator `c = X a X⁻¹ a⁻¹` would satisfy `(c - 1) ^ 2 = 0` and would have order prime to `p`,
hence `c = 1` by `eq_one_of_pow_eq_one_of_sq_sub_one_eq_zero`, contradicting `noncomm`.) -/
lemma restrict_or_quotient_of_coreHyp {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {p : ℕ} [Fact p.Prime] [CharP K p] {Q : Subgroup (Module.End K V)ˣ}
    {X : (Module.End K V)ˣ}
    (h : Work.HallHigman.CoreHyp p Q X) {U : Submodule K V}
    (hQU : ∀ a ∈ Q, ∀ v ∈ U, (a : Module.End K V) v ∈ U)
    (hXU : ∀ v ∈ U, (X : Module.End K V) v ∈ U)
    (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤)
    (hfail : ((X : Module.End K V) - 1) ^ (p - 1) = 0) :
    (∃ (Q' : Subgroup (Module.End K U)ˣ) (X' : (Module.End K U)ˣ),
        Work.HallHigman.CoreHyp p Q' X' ∧ ((X' : Module.End K U) - 1) ^ (p - 1) = 0) ∨
    (∃ (Q'' : Subgroup (Module.End K (V ⧸ U))ˣ) (X'' : (Module.End K (V ⧸ U))ˣ),
        Work.HallHigman.CoreHyp p Q'' X'' ∧
          ((X'' : Module.End K (V ⧸ U)) - 1) ^ (p - 1) = 0) := by
  haveI := h.finite
  have hX : X ∈ stab U := mem_stab_of_pow_eq_one (Fact.out : p.Prime).pos h.pow hXU
  have hQ : Q ≤ stab U := le_stab_of_forall_mapsTo hQU
  by_cases hR : ∃ a ∈ (Q.subgroupOf (stab U)).map (restrHom U),
      a * restrHom U ⟨X, hX⟩ ≠ restrHom U ⟨X, hX⟩ * a
  · left
    exact ⟨_, _, coreHyp_map h hQ hX (restrHom U) hR, restrUnit_sub_one_pow_eq_zero hX hfail⟩
  · by_cases hQq : ∃ a ∈ (Q.subgroupOf (stab U)).map (quotHom U),
        a * quotHom U ⟨X, hX⟩ ≠ quotHom U ⟨X, hX⟩ * a
    · right
      exact ⟨_, _, coreHyp_map h hQ hX (quotHom U) hQq, quotUnit_sub_one_pow_eq_zero hX hfail⟩
    · exfalso
      push_neg at hR hQq
      obtain ⟨a₀, ha₀, hnc⟩ := h.noncomm
      have hcQ : X * a₀ * X⁻¹ * a₀⁻¹ ∈ Q := Q.mul_mem (h.norm a₀ ha₀) (Q.inv_mem ha₀)
      have hcstab : X * a₀ * X⁻¹ * a₀⁻¹ ∈ stab U := hQ hcQ
      have hcomp : (⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩ : stab U)
          = ⟨X, hX⟩ * ⟨a₀, hQ ha₀⟩ * ⟨X, hX⟩⁻¹ * ⟨a₀, hQ ha₀⟩⁻¹ := by
        apply Subtype.ext
        simp [Subgroup.coe_mul, Subgroup.coe_inv]
      have hmemR : restrHom U ⟨a₀, hQ ha₀⟩ ∈ (Q.subgroupOf (stab U)).map (restrHom U) :=
        Subgroup.mem_map.mpr ⟨⟨a₀, hQ ha₀⟩, Subgroup.mem_subgroupOf.mpr ha₀, rfl⟩
      have hmemQ : quotHom U ⟨a₀, hQ ha₀⟩ ∈ (Q.subgroupOf (stab U)).map (quotHom U) :=
        Subgroup.mem_map.mpr ⟨⟨a₀, hQ ha₀⟩, Subgroup.mem_subgroupOf.mpr ha₀, rfl⟩
      have hcommR : restrHom U ⟨a₀, hQ ha₀⟩ * restrHom U ⟨X, hX⟩
          = restrHom U ⟨X, hX⟩ * restrHom U ⟨a₀, hQ ha₀⟩ := hR _ hmemR
      have hcommQ : quotHom U ⟨a₀, hQ ha₀⟩ * quotHom U ⟨X, hX⟩
          = quotHom U ⟨X, hX⟩ * quotHom U ⟨a₀, hQ ha₀⟩ := hQq _ hmemQ
      have hr : restrUnit U ⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩ = 1 := by
        rw [show restrUnit U ⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩
              = restrHom U ⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩ from rfl]
        rw [hcomp, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcommR]
        group
      have hq : quotUnit U ⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩ = 1 := by
        rw [show quotUnit U ⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩
              = quotHom U ⟨X * a₀ * X⁻¹ * a₀⁻¹, hcstab⟩ from rfl]
        rw [hcomp, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcommQ]
        group
      have hsq : ((((X * a₀ * X⁻¹ * a₀⁻¹ : (Module.End K V)ˣ)) : Module.End K V) - 1) ^ 2 = 0 :=
        sq_sub_one_eq_zero_of_restr_eq_one_of_quot_eq_one hcstab hr hq
      have hpow : ((X * a₀ * X⁻¹ * a₀⁻¹ : (Module.End K V)ˣ)) ^ Nat.card Q = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard Q hcQ)
      have hpow' : (((X * a₀ * X⁻¹ * a₀⁻¹ : (Module.End K V)ˣ)) : Module.End K V) ^ Nat.card Q
          = 1 := by
        rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
      have hc_eq : (((X * a₀ * X⁻¹ * a₀⁻¹ : (Module.End K V)ˣ)) : Module.End K V) = 1 :=
        Work.HallHigman.eq_one_of_pow_eq_one_of_sq_sub_one_eq_zero h.cop hpow' hsq
      have hcunit : X * a₀ * X⁻¹ * a₀⁻¹ = 1 := Units.ext hc_eq
      have hxa : X * a₀ = a₀ * X := by
        calc X * a₀ = (X * a₀ * X⁻¹ * a₀⁻¹) * (a₀ * X) := by group
          _ = 1 * (a₀ * X) := by rw [hcunit]
          _ = a₀ * X := by group
      exact hnc hxa.symm

end Work.HallHigman.GLCore
