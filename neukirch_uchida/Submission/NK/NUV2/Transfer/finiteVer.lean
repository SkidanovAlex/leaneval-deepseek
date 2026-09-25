import Mathlib

noncomputable section

namespace NK.NUV2.Transfer

open Subgroup

/-! ## Auxiliary lemmas about the abelianization -/

section Ab

variable {G : Type*} [Group G]

/-- Conjugation is trivial in the abelianization. -/
lemma of_conj (y x : G) : Abelianization.of (y * x * y⁻¹) = Abelianization.of x := by
  rw [map_mul, map_mul, map_inv, mul_comm (Abelianization.of y) (Abelianization.of x),
    mul_assoc, mul_inv_cancel, mul_one]

lemma of_conj_inv (y x : G) : Abelianization.of (y⁻¹ * x * y) = Abelianization.of x := by
  rw [show y⁻¹ * x * y = y⁻¹ * x * (y⁻¹)⁻¹ from by group, of_conj]

end Ab

lemma map_subtype_of_mk {G : Type*} [Group G] (H : Subgroup G) (a : G) (ha : a ∈ H) :
    Abelianization.map H.subtype (Abelianization.of (⟨a, ha⟩ : ↥H)) = Abelianization.of a := by
  rw [Abelianization.map_of]
  rfl

lemma Finset.univ_congr {α : Type*} (i j : Fintype α) : @Finset.univ α i = @Finset.univ α j := by
  rw [Subsingleton.elim i j]

/-! ## The transfer formula for elements of `H` -/

section Transfer

variable {G : Type*} [Group G] {H : Subgroup G} [H.Normal] [H.FiniteIndex] [Fintype (G ⧸ H)]

lemma smul_eq_self_of_mem {h : G} (hh : h ∈ H) (q : G ⧸ H) : h • q = q := by
  induction q using QuotientGroup.induction_on with
  | _ g =>
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul, mul_inv_rev]
    exact Subgroup.Normal.conj_mem' (inferInstance : H.Normal) h⁻¹ (H.inv_mem hh) g

lemma out_inv_mem (h : H) (q : G ⧸ H) :
    (Quotient.out q)⁻¹ * (h : G) * Quotient.out q ∈ H := by
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq']
  rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk (H := H) (h : G) (Quotient.out q),
    QuotientGroup.out_eq']
  exact (smul_eq_self_of_mem h.2 q).symm

lemma diff_factor_eq (h : H) (q : G ⧸ H) :
    ((default : H.LeftTransversal).2.leftQuotientEquiv q : G)⁻¹ *
      (((h : G) • (default : H.LeftTransversal)).2.leftQuotientEquiv q : G)
      = (Quotient.out q)⁻¹ * (h : G) * Quotient.out q := by
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul,
    Subgroup.IsComplement.leftQuotientEquiv_apply Quotient.out_eq',
    Subgroup.IsComplement.leftQuotientEquiv_apply Quotient.out_eq']
  rw [smul_eq_self_of_mem (H.inv_mem h.2) q, mul_assoc]

/-- The transfer of an element of `H`, computed with the canonical transversal. -/
lemma transfer_apply_of_mem {A : Type*} [CommGroup A] (ϕ : ↥H →* A) (h : H) :
    MonoidHom.transfer ϕ (h : G) =
      ∏ q : G ⧸ H, ϕ ⟨(Quotient.out q)⁻¹ * (h : G) * Quotient.out q, out_inv_mem h q⟩ := by
  rw [MonoidHom.transfer_def ϕ (default : H.LeftTransversal) (h : G)]
  unfold Subgroup.leftTransversals.diff
  dsimp only
  refine Finset.prod_congr (Finset.univ_congr _ _) (fun q _ => ?_)
  exact congrArg ϕ (Subtype.ext (diff_factor_eq h q))

end Transfer

/-! ## The composite `Gᵃᵇ → Hᵃᵇ → Gᵃᵇ` -/

section FirstPart

variable {G : Type*} [Group G] [Fintype G] {H : Subgroup G} [H.Normal] [H.FiniteIndex]
  [Fintype (G ⧸ H)]

lemma transfer_factor (g : G) (q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)))
    (ha : (Quotient.out q.out)⁻¹ * g ^ Function.minimalPeriod (fun x => g • x) q.out
      * Quotient.out q.out ∈ H) :
    Abelianization.map H.subtype
      (Abelianization.of ⟨(Quotient.out q.out)⁻¹ * g ^ Function.minimalPeriod (fun x => g • x) q.out
        * Quotient.out q.out, ha⟩)
      = Abelianization.of g ^ Function.minimalPeriod (fun x => g • x) q.out := by
  rw [map_subtype_of_mk, of_conj_inv, map_pow]

lemma prod_pow_sum_univ {ι M : Type*} [Fintype ι] [CommMonoid M] (f : ι → ℕ) (a : M) :
    (∏ i, a ^ f i) = a ^ (∑ i, f i) := by
  rw [← Finset.prod_pow_eq_pow_sum Finset.univ f a]

/-- The composite `Gᵃᵇ → Hᵃᵇ → Gᵃᵇ` is the index-th power map. -/
theorem map_subtype_transfer (g : G) :
    Abelianization.map H.subtype
      (MonoidHom.transfer (Abelianization.of : ↥H →* Abelianization H) g)
      = Abelianization.of g ^ H.index := by
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :=
    Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, map_prod]
  rw [show (∏ x, (Abelianization.map H.subtype)
        (Abelianization.of ⟨(Quotient.out x.out)⁻¹ * g ^ Function.minimalPeriod (fun x => g • x) x.out
          * Quotient.out x.out, QuotientGroup.out_conj_pow_minimalPeriod_mem H g x.out⟩))
      = ∏ x, Abelianization.of g ^ Function.minimalPeriod (fun x => g • x) x.out from
    Finset.prod_congr rfl (fun x _ => transfer_factor g x _)]
  rw [prod_pow_sum_univ, Subgroup.index_eq_sum_minimalPeriod H g]

end FirstPart

/-! ## The composite `Hᵃᵇ → Gᵃᵇ → Hᵃᵇ` -/

section SecondPart

variable {G : Type*} [Group G] [Fintype G] {H : Subgroup G} [H.Normal] [H.FiniteIndex]
  [Fintype (G ⧸ H)]

/-- The inversion bijection on the quotient group. -/
noncomputable def invEquiv : (G ⧸ H) ≃ (G ⧸ H) where
  toFun q := q⁻¹
  invFun q := q⁻¹
  left_inv q := inv_inv q
  right_inv q := inv_inv q

lemma conj_mem (h : H) (t : G) : t * (h : G) * t⁻¹ ∈ H :=
  Subgroup.Normal.conj_mem (inferInstance : H.Normal) (h : G) h.2 t

/-- `conjNormal` applied to `h` agrees for two representatives of the same coset. -/
lemma of_conjNormal_eq_of_mem (h : H) {u u' : G} (hu : u'⁻¹ * u ∈ H) :
    Abelianization.of (MulAut.conjNormal u h) = Abelianization.of (MulAut.conjNormal u' h) := by
  obtain ⟨w, hwmem, hw⟩ : ∃ w : G, w ∈ H ∧ u = u' * w := ⟨u'⁻¹ * u, hu, by group⟩
  rw [hw]
  have h1 : MulAut.conjNormal (u' * w) h = MulAut.conjNormal u' (MulAut.conjNormal w h) := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply, MulAut.conjNormal_apply]
    group
  have h2 : Abelianization.of (MulAut.conjNormal w h) = Abelianization.of h := by
    rw [show MulAut.conjNormal w h = (⟨w, hwmem⟩ : ↥H) * h * (⟨w, hwmem⟩ : ↥H)⁻¹ from
      Subtype.ext (MulAut.conjNormal_apply w h)]
    exact of_conj _ _
  have h3 : Abelianization.map (MulAut.conjNormal (H := H) u' : ↥H →* ↥H)
        (Abelianization.of (MulAut.conjNormal w h))
      = Abelianization.of (MulAut.conjNormal u' h) :=
    (congrArg (Abelianization.map (MulAut.conjNormal (H := H) u' : ↥H →* ↥H)) h2).trans
      (Abelianization.map_of (MulAut.conjNormal (H := H) u' : ↥H →* ↥H) h)
  calc Abelianization.of (MulAut.conjNormal (u' * w) h)
      = Abelianization.of (MulAut.conjNormal u' (MulAut.conjNormal w h)) := by rw [h1]
    _ = Abelianization.map (MulAut.conjNormal (H := H) u' : ↥H →* ↥H)
          (Abelianization.of (MulAut.conjNormal w h)) :=
        (Abelianization.map_of (MulAut.conjNormal (H := H) u' : ↥H →* ↥H)
          (MulAut.conjNormal w h)).symm
    _ = Abelianization.of (MulAut.conjNormal u' h) := h3

lemma map_conjNormal_eq_of_mem (h : H) {u u' : G} (hu : u'⁻¹ * u ∈ H) :
    Abelianization.map (MulAut.conjNormal (H := H) u : ↥H →* ↥H) (Abelianization.of h)
      = Abelianization.map (MulAut.conjNormal (H := H) u' : ↥H →* ↥H) (Abelianization.of h) := by
  rw [Abelianization.map_of (MulAut.conjNormal (H := H) u : ↥H →* ↥H) h,
    Abelianization.map_of (MulAut.conjNormal (H := H) u' : ↥H →* ↥H) h]
  exact of_conjNormal_eq_of_mem h hu

lemma out_invEquiv_mem (q : G ⧸ H) :
    ((Quotient.out (invEquiv (H := H) q))⁻¹ : G)⁻¹ * Quotient.out q ∈ H := by
  have key : (↑((Quotient.out (invEquiv (H := H) q))⁻¹) : G ⧸ H) = ↑(Quotient.out q) := by
    rw [QuotientGroup.mk_inv, QuotientGroup.out_eq', QuotientGroup.out_eq']
    exact inv_inv q
  exact QuotientGroup.leftRel_apply.mp (Quotient.exact' key)

lemma of_conjNormal_map (h : H) (t : G) :
    Abelianization.map (MulAut.conjNormal (H := H) t : ↥H →* ↥H) (Abelianization.of h)
      = Abelianization.of (MulAut.conjNormal t h) :=
  Abelianization.map_of (MulAut.conjNormal (H := H) t : ↥H →* ↥H) h

lemma mk_conjNormal_eq (h : H) (t : G) (ht : t⁻¹ * (h : G) * t ∈ H) :
    (⟨t⁻¹ * (h : G) * t, ht⟩ : ↥H) = MulAut.conjNormal t⁻¹ h := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, inv_inv]

end SecondPart

/-! ## The main theorem -/

theorem finiteVer {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [H.Normal] [H.FiniteIndex]
    [Fintype (G ⧸ H)] :
    (∀ x : Abelianization G,
        Abelianization.map H.subtype
          (Abelianization.lift (MonoidHom.transfer (H := H) (Abelianization.of : ↥H →* Abelianization H)) x)
        = x ^ H.index) ∧
    (∀ x : Abelianization H,
        Abelianization.lift (MonoidHom.transfer (H := H) (Abelianization.of : ↥H →* Abelianization H))
          (Abelianization.map H.subtype x)
        = ∏ q : G ⧸ H,
            Abelianization.map ((MulAut.conjNormal (H := H) (Quotient.out q) : ↥H →* ↥H)) x) := by
  constructor
  · intro x
    have hF : (Abelianization.map H.subtype).comp
          (Abelianization.lift (MonoidHom.transfer (H := H) (Abelianization.of : ↥H →* Abelianization H)))
        = powMonoidHom H.index := by
      refine Abelianization.hom_ext _ _ ?_
      ext g
      simpa using map_subtype_transfer g
    simpa using (DFunLike.congr_fun hF x).trans (powMonoidHom_apply H.index x)
  · intro x
    induction x using QuotientGroup.induction_on' with
    | _ h =>
      change Abelianization.lift
            (MonoidHom.transfer (H := H) (Abelianization.of : ↥H →* Abelianization H))
            (Abelianization.map H.subtype (Abelianization.of h))
          = ∏ q : G ⧸ H,
              Abelianization.map ((MulAut.conjNormal (H := H) (Quotient.out q) : ↥H →* ↥H))
                (Abelianization.of h)
      calc Abelianization.lift
              (MonoidHom.transfer (H := H) (Abelianization.of : ↥H →* Abelianization H))
              (Abelianization.map H.subtype (Abelianization.of h))
          = MonoidHom.transfer (H := H) (Abelianization.of : ↥H →* Abelianization H) (h : G) := by
            rw [Abelianization.map_of, Abelianization.lift_apply_of]
            rfl
        _ = ∏ q : G ⧸ H, Abelianization.of
              (⟨(Quotient.out q)⁻¹ * (h : G) * Quotient.out q, out_inv_mem h q⟩ : ↥H) := by
            rw [transfer_apply_of_mem]
        _ = ∏ q : G ⧸ H, Abelianization.map
              (MulAut.conjNormal (H := H) ((Quotient.out q)⁻¹) : ↥H →* ↥H)
              (Abelianization.of h) := by
            refine Finset.prod_congr rfl (fun q _ => ?_)
            rw [congrArg (fun z : ↥H => Abelianization.of z)
              (mk_conjNormal_eq h (Quotient.out q) (out_inv_mem h q))]
            exact (of_conjNormal_map h ((Quotient.out q)⁻¹)).symm
        _ = ∏ q : G ⧸ H, Abelianization.map
              (MulAut.conjNormal (H := H) (Quotient.out q) : ↥H →* ↥H)
              (Abelianization.of h) := by
            refine (Fintype.prod_equiv (invEquiv (H := H)) _ _
              (fun q => map_conjNormal_eq_of_mem h (out_invEquiv_mem q))).symm

end NK.NUV2.Transfer
