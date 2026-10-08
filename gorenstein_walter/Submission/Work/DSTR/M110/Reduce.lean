import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.M110.Conj
import Submission.Work.DSTR.map_fittingPiIn_le
import Submission.Work.DSTR.M110.conjHom_surjective

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Work.DSTR

open Subgroup Work.AUTL2

/-- `pslHom F` is injective. -/
theorem pslHom_injective (F : Type*) [Field F] [DecidableEq F] :
    Function.Injective (Work.AUTL2.pslHom F) := by
  intro a b h
  exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    (Work.AUTL2.Aut.pglHomInjective F h)

/-- The spatiality statement A6, as a `Prop`: every automorphism of `PSL(2,q)` (in the `ℙ¹`
permutation model) is conjugation by an element of `PΓL(2,q)`. -/
def A6Prop : Prop := ∀ (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)] (hp : Odd p)
    (hq : 5 ≤ p ^ k) [DecidableEq (GaloisField p k)],
    Function.Surjective (Work.AUTL2.conjHom (GaloisField p k))

/-- DS10a in the `ℙ¹` permutation model: for an overgroup `Q'` of `PSL(2,q)` inside `PΓL(2,q)`,
`F_{2'}(C_{Q'}(t')) ≤ PSL(2,q)` for every involution `t'`. -/
def CruxProp : Prop := ∀ (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (Q' : Subgroup (Equiv.Perm (P1 (GaloisField p k))))
    (hpsl : pslImage (GaloisField p k) ≤ Q') (hQ : Q' ≤ pgammaL (GaloisField p k))
    (t' : Q') (ht' : orderOf t' = 2),
    Work.GW2.fittingPiIn {2}ᶜ (Subgroup.centralizer ({t'} : Set Q'))
      ≤ (pslImage (GaloisField p k)).subgroupOf Q'

/-- The isomorphism `PSL(2,F) ≃* ↥(pslImage F)` given by `pslHom`. -/
noncomputable def pslIso (F : Type*) [Field F] [DecidableEq F] :
    PSL(2, F) ≃* ↥(Work.AUTL2.pslImage F) :=
  MulEquiv.ofBijective ((Work.AUTL2.pslHom F).rangeRestrict)
    ⟨fun a b h => pslHom_injective F (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

/-- The isomorphism `↥L ≃* ↥(pslImage F)` induced by an isomorphism `L ≃* PSL(2,F)`. -/
noncomputable def pslImageIso {F : Type*} [Field F] [DecidableEq F]
    {L : Type*} [Group L] (e : L ≃* PSL(2, F)) :
    L ≃* ↥(Work.AUTL2.pslImage F) :=
  e.trans (pslIso F)

/-- `F_{2'}` is preserved by an isomorphism of groups. -/
theorem fittingPiIn_map_mulEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (φ : G ≃* H) (K : Subgroup G) :
    (Work.GW2.fittingPiIn {n : ℕ | n ≠ 2} K).map (φ : G →* H)
      = Work.GW2.fittingPiIn {n : ℕ | n ≠ 2} (K.map (φ : G →* H)) := by
  refine le_antisymm (map_fittingPiIn_le (φ : G →* H) φ.surjective K) ?_
  have h := map_fittingPiIn_le (φ.symm : H →* G) φ.symm.surjective (K.map (φ : G →* H))
  have e1 : (K.map (φ : G →* H)).map (φ.symm : H →* G) = K := by
    rw [Subgroup.map_map]
    have : (φ.symm : H →* G).comp (φ : G →* H) = MonoidHom.id G := by ext x; simp
    rw [this, Subgroup.map_id]
  rw [e1] at h
  have h2 := Subgroup.map_mono (f := (φ : G →* H)) h
  have e2 : ((Work.GW2.fittingPiIn {n : ℕ | n ≠ 2} (K.map (φ : G →* H))).map
      (φ.symm : H →* G)).map (φ : G →* H)
      = Work.GW2.fittingPiIn {n : ℕ | n ≠ 2} (K.map (φ : G →* H)) := by
    rw [Subgroup.map_map]
    have : (φ : G →* H).comp (φ.symm : H →* G) = MonoidHom.id H := by ext x; simp
    rw [this, Subgroup.map_id]
  rw [e2] at h2
  exact h2


/-- `A6Prop` holds (from the spatiality theorem). -/
theorem a6Prop : A6Prop := fun p k _ _ hp hq _ => Work.DSTR.M110.conjHom_surjective p k hp hq

/-- The inclusion `PSL(2,F) ≤ PΓL(2,F)` as a monoid homomorphism. -/
noncomputable def pslToPgammaL (F : Type*) [Field F] [DecidableEq F] :
    ↥(pslImage F) →* ↥(pgammaL F) :=
  Subgroup.inclusion (pslImage_le_pglImage F |>.trans le_sup_left)

@[simp] lemma pslToPgammaL_apply (F : Type*) [Field F] [DecidableEq F]
    (x : ↥(pslImage F)) :
    ((pslToPgammaL F x : ↥(pgammaL F)) : Equiv.Perm (P1 F)) = x := rfl


open Classical in
/-- **Reduction**: assuming `A6Prop` (spatiality) and `CruxProp` (DS10a in the `ℙ¹` model),
the abstract contract `D110iiModelProp` holds. -/
theorem d110iiModel_of (ha6 : A6Prop) (hcrux : CruxProp) : Work.GW2.D110iiModelProp := by
  intro Q _instG _instF L p k _instFact hp hq hnorm he hcent hsyl t ht
  obtain ⟨e⟩ := he
  haveI hLnorm : L.Normal := hnorm
  haveI hFt : Fintype (GaloisField p k) := Fintype.ofFinite _
  haveI hDd : DecidableEq (GaloisField p k) := Classical.decEq _
  let ρ : Q →* MulAut ↥L := MulAut.conjNormal (H := L)
  have hρker : ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    rw [MonoidHom.mem_ker] at hq
    rw [Subgroup.mem_bot]
    have hmem : q ∈ Subgroup.centralizer (L : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h2 : ρ q ⟨h, hh⟩ = ⟨h, hh⟩ := by rw [hq]; rfl
      have h3 := congrArg Subtype.val h2
      simp only [ρ, MulAut.conjNormal_apply] at h3
      have : q * h = h * q := by
        calc q * h = (q * h * q⁻¹) * q := by group
          _ = h * q := by rw [h3]
      exact this.symm
    rw [hcent] at hmem
    rwa [Subgroup.mem_bot] at hmem
  have hρinj : Function.Injective ρ := MonoidHom.ker_eq_bot_iff _ |>.mp hρker
  let ψ : ↥L ≃* ↥(pslImage (GaloisField p k)) := pslImageIso e
  let c : MulAut ↥L ≃* MulAut ↥(pslImage (GaloisField p k)) := MulAut.congr ψ
  have hsurj : Function.Surjective (conjHom (GaloisField p k)) := ha6 p k hp hq
  let φ₀ : Q →* pgammaL (GaloisField p k) :=
    ((conjHomEquiv p k hp hq hsurj).toMonoidHom).comp (c.toMonoidHom.comp ρ)
  let φ : Q →* Equiv.Perm (P1 (GaloisField p k)) := (pgammaL (GaloisField p k)).subtype.comp φ₀
  have hconjHom_eq : ∀ x : ↥(pslImage (GaloisField p k)),
      conjHom (GaloisField p k) (pslToPgammaL (GaloisField p k) x) = MulAut.conj x := by
    intro x
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    simp only [conjHom_apply, conjAut_apply, MulAut.conj_apply, pslToPgammaL_apply,
      Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  have hφl : ∀ l : ↥L, φ l = (ψ l : Equiv.Perm (P1 (GaloisField p k))) := by
    intro l
    have h1 : c (ρ (l : Q)) = MulAut.conj (ψ l) := by
      rw [show ρ (l : Q) = MulAut.conj (l : ↥L) from MulAut.conjNormal_val (H := L)]
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      simp only [c, MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply,
        MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply, map_mul, map_inv, Subgroup.coe_mul,
        Subgroup.coe_inv, Subtype.coe_mk]
    have h3 : conjHom (GaloisField p k) (conjHomEquiv p k hp hq hsurj (c (ρ (l : Q)))) =
        c (ρ (l : Q)) := conjHom_conjHomEquiv p k hp hq hsurj _
    have h4 : conjHomEquiv p k hp hq hsurj (c (ρ (l : Q))) =
        pslToPgammaL (GaloisField p k) (ψ l) := by
      apply conjHom_injective p k hp hq
      rw [h3, hconjHom_eq]
      exact h1
    show ((conjHomEquiv p k hp hq hsurj (c (ρ (l : Q))) : pgammaL (GaloisField p k)) :
      Equiv.Perm (P1 (GaloisField p k))) = _
    rw [h4]
    rfl
  have hφLmem : ∀ x : Equiv.Perm (P1 (GaloisField p k)),
      x ∈ pslImage (GaloisField p k) ↔ ∃ l : ↥L, φ l = x := by
    intro x
    constructor
    · intro hx
      refine ⟨ψ.symm ⟨x, hx⟩, ?_⟩
      rw [hφl]
      exact congrArg Subtype.val (MulEquiv.apply_symm_apply ψ ⟨x, hx⟩)
    · rintro ⟨l, rfl⟩
      rw [hφl l]
      exact (ψ l).2
  have hφinj₀ : Function.Injective φ₀ := by
    intro a b hab
    have h1 : c (ρ a) = c (ρ b) :=
      (conjHomEquiv p k hp hq hsurj).injective hab
    exact hρinj (c.injective h1)
  have hφinj : Function.Injective φ := by
    intro a b hab
    exact hφinj₀ (Subtype.ext hab)
  let Q' : Subgroup (Equiv.Perm (P1 (GaloisField p k))) := φ.range
  let φ' : Q ≃* Q' := MulEquiv.ofBijective (φ.rangeRestrict)
    ⟨fun a b h => hφinj (by simpa only [MonoidHom.coe_rangeRestrict] using congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩
  have hφ'val : ∀ q : Q, ((φ' q : Q') : Equiv.Perm (P1 (GaloisField p k))) = φ q := fun q => rfl
  have hpsl : pslImage (GaloisField p k) ≤ Q' := by
    intro x hx
    obtain ⟨l, hl⟩ := (hφLmem x).mp hx
    exact ⟨l, hl⟩
  have hQle : Q' ≤ pgammaL (GaloisField p k) := by
    rintro x ⟨y, -, rfl⟩
    exact (φ₀ y).2
  have ht' : orderOf (φ' t) = 2 := (MulEquiv.orderOf_eq φ' t).trans ht
  have hcrux' := hcrux p k hp hq Q' hpsl hQle (φ' t) ht'
  have hLmap : L.map (φ' : Q →* Q') = (pslImage (GaloisField p k)).subgroupOf Q' := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      change ((φ' l : Q') : Equiv.Perm (P1 (GaloisField p k))) ∈ pslImage (GaloisField p k)
      rw [hφ'val l, hφl ⟨l, hl⟩]
      exact (ψ ⟨l, hl⟩).2
    · intro hx
      obtain ⟨l, hl⟩ := (hφLmem (x : Equiv.Perm (P1 (GaloisField p k)))).mp hx
      refine ⟨l, l.2, ?_⟩
      apply Subtype.ext
      change ((φ' l : Q') : Equiv.Perm (P1 (GaloisField p k))) =
        (x : Equiv.Perm (P1 (GaloisField p k)))
      rw [hφ'val l, hl]
  have hcentmap : (Subgroup.centralizer ({t} : Set Q)).map (φ' : Q →* Q')
      = Subgroup.centralizer ({φ' t} : Set Q') := by
    refine le_antisymm ?_ ?_
    · convert Subgroup.map_centralizer_le_centralizer_image {t} (φ' : Q →* Q') using 1
      rw [Set.image_singleton]
      rfl
    · intro y hy
      rw [Subgroup.mem_map]
      rw [Subgroup.mem_centralizer_iff] at hy
      have hyt : φ' t * y = y * φ' t := hy (φ' t) (Set.mem_singleton _)
      obtain ⟨q, hq⟩ := y.2
      have hq' : φ' q = y := Subtype.ext hq
      refine ⟨q, ?_, hq'⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      apply φ'.injective
      rw [map_mul, map_mul, hq']
      exact hyt
  have hNle : Work.GW2.fittingPiIn {2}ᶜ (Subgroup.centralizer ({t} : Set Q)) ≤ L := by
    have hNmap := fittingPiIn_map_mulEquiv φ' (Subgroup.centralizer ({t} : Set Q))
    rw [hcentmap] at hNmap
    rw [show ({2}ᶜ : Set ℕ) = {n : ℕ | n ≠ 2} from by ext n; simp] at hcrux'
    rw [← hNmap, ← hLmap] at hcrux'
    exact Subgroup.map_le_map_iff_of_injective φ'.injective |>.mp hcrux'
  exact hNle

end Work.DSTR
