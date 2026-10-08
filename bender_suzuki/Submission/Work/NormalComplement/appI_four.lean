import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.appI_kapp_ncard
import Submission.Work.Coprime.Internal
import Submission.Work.Coprime.commutator_fixedPoints_sup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

open scoped Pointwise
open scoped commutatorElement

namespace Work.NormalComplement

variable {G : Type*} [Group G] [Finite G]

/-! ## Basic setup for the action of `t` on `X`

Every lemma in this section is an ingredient of Peterfalvi's Appendix I (4) for the
action of an element `t` of prime order `d` on a finite `d'`-subgroup `X` normalised by `t`.
-/

/-- `t` normalises `X` *as a subgroup*: `t X t⁻¹ = X` (the reverse inclusion uses finiteness). -/
lemma conjX_eq {t : G} {X : Subgroup G} (htX : NormalizedBy t X) :
    X.map (MulAut.conj t).toMonoidHom = X := by
  have hle : X.map (MulAut.conj t).toMonoidHom ≤ X := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    simpa [MulAut.conj_apply] using htX x hx
  have hcard : Nat.card ↥(X.map (MulAut.conj t).toMonoidHom) = Nat.card ↥X :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

/-- `t⁻¹ x t ∈ X` for `x ∈ X` (the "inverse" half of `NormalizedBy`, via finiteness). -/
lemma inv_conj_mem {t : G} {X : Subgroup G} (htX : NormalizedBy t X) {x : G} (hx : x ∈ X) :
    t⁻¹ * x * t ∈ X := by
  have hx' : x ∈ X.map (MulAut.conj t).toMonoidHom := by rw [conjX_eq htX]; exact hx
  obtain ⟨z, hz, hz'⟩ := Subgroup.mem_map.mp hx'
  have hzx : z = t⁻¹ * x * t := by
    have h := hz'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [← h]; group
  rw [← hzx]; exact hz

/-- App. I (4): `K ⊆ X`. -/
lemma Kapp_subset {t : G} {X : Subgroup G} (htX : NormalizedBy t X) :
    Kapp t X ⊆ (X : Set G) := by
  rintro z ⟨x, hx, rfl⟩
  exact X.mul_mem (inv_conj_mem htX (X.inv_mem hx)) hx

/-- App. I (4): `V = C_X(t)` normalises `K = Kapp t X`. -/
lemma Kapp_conj_centralizer {t : G} {X : Subgroup G}
    (k : G) (hk : k ∈ Kapp t X) (v : G)
    (hv : v ∈ Subgroup.centralizer ({t} : Set G) ⊓ X) :
    v * k * v⁻¹ ∈ Kapp t X := by
  obtain ⟨hvc, hvX⟩ := hv
  obtain ⟨x, hxX, rfl⟩ := hk
  have hvt : t * v = v * t := (Subgroup.mem_centralizer_iff.mp hvc) t (Set.mem_singleton t)
  have hv1 : v * t * v⁻¹ = t := by rw [← hvt]; group
  refine ⟨v * x * v⁻¹, X.mul_mem (X.mul_mem hvX hxX) (X.inv_mem hvX), ?_⟩
  have key : v * (t⁻¹ * x⁻¹ * t * x) * v⁻¹
      = t⁻¹ * (v * x * v⁻¹)⁻¹ * t * (v * x * v⁻¹) := by
    have h : (MulAut.conj v) (t⁻¹ * x⁻¹ * t * x)
        = t⁻¹ * ((MulAut.conj v) x)⁻¹ * t * ((MulAut.conj v) x) := by
      simp only [map_mul, map_inv]
      rw [show (MulAut.conj v) t = t from hv1]
    simpa [MulAut.conj_apply] using h
  rw [key]

/-- The identity `[t,y]^{x₀} = [t,x₀⁻¹]⁻¹[t,y x₀⁻¹]` of App. I (4): conjugation by `x₀ ∈ X`
sends every element of `Kapp t X` into `⟨Kapp t X⟩`. -/
lemma Kapp_conj_normal {t : G} {X : Subgroup G}
    (x0 : G) (hx0 : x0 ∈ X) (k : G) (hk : k ∈ Kapp t X) :
    x0 * k * x0⁻¹ ∈ Subgroup.closure (Kapp t X) := by
  obtain ⟨y, hyX, rfl⟩ := hk
  have h1 : x0⁻¹ ∈ X := X.inv_mem hx0
  have h2 : y * x0⁻¹ ∈ X := X.mul_mem hyX h1
  have hmem1 : t⁻¹ * (x0⁻¹)⁻¹ * t * (x0⁻¹) ∈ Kapp t X := ⟨x0⁻¹, h1, rfl⟩
  have hmem2 : t⁻¹ * (y * x0⁻¹)⁻¹ * t * (y * x0⁻¹) ∈ Kapp t X := ⟨y * x0⁻¹, h2, rfl⟩
  have key : x0 * (t⁻¹ * y⁻¹ * t * y) * x0⁻¹
      = (t⁻¹ * (x0⁻¹)⁻¹ * t * (x0⁻¹))⁻¹ * (t⁻¹ * (y * x0⁻¹)⁻¹ * t * (y * x0⁻¹)) := by
    group
  rw [key]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure hmem1))
    (Subgroup.subset_closure hmem2)

/-- App. I (4): `⟨Kapp t X⟩ ⊴ X`. -/
lemma Kapp_conj_normal' {t : G} {X : Subgroup G}
    (x0 : G) (hx0 : x0 ∈ X) :
    ∀ k ∈ Subgroup.closure (Kapp t X), x0 * k * x0⁻¹ ∈ Subgroup.closure (Kapp t X) := by
  intro k hk
  refine Subgroup.closure_induction (p := fun k _ => x0 * k * x0⁻¹ ∈ Subgroup.closure (Kapp t X))
    (fun z hz => Kapp_conj_normal x0 hx0 z hz) ?_ ?_ ?_ hk
  · simp
  · intro a b _ _ ha hb
    rw [show x0 * (a * b) * x0⁻¹ = (x0 * a * x0⁻¹) * (x0 * b * x0⁻¹) from by group]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [show x0 * a⁻¹ * x0⁻¹ = (x0 * a * x0⁻¹)⁻¹ from by group]
    exact Subgroup.inv_mem _ ha

/-- App. I (4): `t` normalises `K = Kapp t X`. -/
lemma t_normalizes_Kapp {t : G} {X : Subgroup G} (htX : NormalizedBy t X) :
    ∀ k ∈ Kapp t X, t * k * t⁻¹ ∈ Kapp t X := by
  rintro z ⟨x, hxX, rfl⟩
  refine ⟨t * x * t⁻¹, htX x hxX, ?_⟩
  group

/-- App. I (4): `t` normalises `⟨Kapp t X⟩`. -/
lemma t_normalizes_K {t : G} {X : Subgroup G} (htX : NormalizedBy t X) :
    ∀ k ∈ Subgroup.closure (Kapp t X), t * k * t⁻¹ ∈ Subgroup.closure (Kapp t X) := by
  intro k hk
  refine Subgroup.closure_induction (p := fun k _ => t * k * t⁻¹ ∈ Subgroup.closure (Kapp t X))
    (fun z hz => Subgroup.subset_closure (t_normalizes_Kapp htX z hz)) ?_ ?_ ?_ hk
  · simp
  · intro a b _ _ ha hb
    rw [show t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) from by group]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [show t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ from by group]
    exact Subgroup.inv_mem _ ha

/-! ## `⟨Kapp t X⟩` is the commutator subgroup `[X, ⟨t⟩]` -/

lemma closure_Kapp_le_normalizer {t : G} {X : Subgroup G} (htX : NormalizedBy t X) :
    Subgroup.zpowers t ≤ Subgroup.normalizer ((Subgroup.closure (Kapp t X)) : Set G) := by
  have hKinv : (Subgroup.closure (Kapp t X)).map (MulAut.conj t).toMonoidHom =
      Subgroup.closure (Kapp t X) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (le_of_eq ?_)
    · rw [Subgroup.map_le_iff_le_comap]
      intro z hz
      exact t_normalizes_K htX z hz
    · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => t_normalizes_K htX h hh
  · intro hh
    have hmem : t * h * t⁻¹ ∈
        (Subgroup.closure (Kapp t X)).map (MulAut.conj t).toMonoidHom := by
      rw [hKinv]; exact hh
    obtain ⟨z, hz, hz'⟩ := Subgroup.mem_map.mp hmem
    have hzh : z = h := by
      have h2 : t * z * t⁻¹ = t * h * t⁻¹ := by
        simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hz'
      exact mul_left_cancel (mul_right_cancel h2)
    rw [← hzh]; exact hz

lemma commutator_zpowers_eq_closure_Kapp {t : G} {X : Subgroup G} (htX : NormalizedBy t X) :
    ⁅X, Subgroup.zpowers t⁆ = Subgroup.closure (Kapp t X) := by
  have hnorm : Subgroup.closure ({t} : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure (Kapp t X)) : Set G) := by
    rw [← Subgroup.zpowers_eq_closure]
    exact closure_Kapp_le_normalizer htX
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hxX s hs
    rw [Subgroup.zpowers_eq_closure] at hs
    refine Subgroup.closure_induction (p := fun s _ => ⁅x, s⁆ ∈ Subgroup.closure (Kapp t X))
      ?_ ?_ ?_ ?_ hs
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Subgroup.subset_closure ⟨t * x⁻¹ * t⁻¹, htX x⁻¹ (X.inv_mem hxX), by
        simp only [commutatorElement_def]; group⟩
    · simp
    · intro a b ha_mem _ ha_ih hb_ih
      rw [commutatorElement_mul_right_eq_mul_conj,
        show ⁅x, a⁆ * a * ⁅x, b⁆ * a⁻¹ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) from by group]
      exact Subgroup.mul_mem _ ha_ih
        ((Subgroup.mem_normalizer_iff.mp (hnorm ha_mem) ⁅x, b⁆).mp hb_ih)
    · intro a ha_mem ha_ih
      rw [commutatorElement_inv_right, ← commutatorElement_inv]
      have hkey := (Subgroup.mem_normalizer_iff.mp (hnorm (Subgroup.inv_mem _ ha_mem))
        ⁅x, a⁆⁻¹).mp (Subgroup.inv_mem _ ha_ih)
      simpa using hkey
  · refine (Subgroup.closure_le ⁅X, Subgroup.zpowers t⁆).mpr ?_
    rintro z ⟨y, hyX, rfl⟩
    have hmem : ⁅t⁻¹, y⁻¹⁆ ∈ ⁅Subgroup.zpowers t, X⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (Subgroup.mem_zpowers t))
        (X.inv_mem hyX)
    rw [Subgroup.commutator_comm] at hmem
    simpa [commutatorElement_def] using hmem

/-! ## The coprime-action decomposition `X = ⟨Kapp t X⟩ · C_X(t)` -/

theorem closure_Kapp_sup_centralizer_aux {d : ℕ} (hd : d.Prime) {t : G} (ht : orderOf t = d)
    {X : Subgroup G} (htX : NormalizedBy t X) (hdX : Nat.Coprime (Nat.card X) d) :
    Subgroup.closure (Kapp t X) ⊔ (Subgroup.centralizer ({t} : Set G) ⊓ X) = X := by
  haveI hN : FT.Normalizes (Subgroup.zpowers t) X := by
    refine ⟨?_⟩
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => htX h hh
    · intro hh
      have hh' : t * h * t⁻¹ ∈ X.map (MulAut.conj t).toMonoidHom := by
        rw [conjX_eq htX]; exact hh
      obtain ⟨z, hz, hz'⟩ := Subgroup.mem_map.mp hh'
      have hzh : z = h := by
        have h2 : t * z * t⁻¹ = t * h * t⁻¹ := by
          simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hz'
        exact mul_left_cancel (mul_right_cancel h2)
      rw [← hzh]; exact hz
  have hcop : (Nat.card ↥(Subgroup.zpowers t)).Coprime (Nat.card ↥X) := by
    rw [Nat.card_zpowers, ht]; exact hdX.symm
  have hsol : Group.IsSolvable ↥(Subgroup.zpowers t) ∨ Group.IsSolvable ↥X := by
    left
    refine Group.isSolvable_of_comm (fun a b => ?_)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
    refine Subtype.ext ?_
    show (a : G) * (b : G) = (b : G) * (a : G)
    rw [← hm, ← hn]
    exact zpow_mul_comm t m n
  have hmain := Work.Coprime.commutator_fixedPoints_sup ↥(Subgroup.zpowers t) (G := ↥X) hcop hsol
  have hmap := congrArg (Subgroup.map X.subtype) hmain
  rw [Subgroup.map_sup] at hmap
  rw [show (⊤ : Subgroup ↥X).map X.subtype = X from by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]] at hmap
  rw [FT.map_fixedPoints_conjAction (Subgroup.zpowers t) X,
      FT.commutator_conjAction (Subgroup.zpowers t) X] at hmap
  have hcent : Subgroup.centralizer (((Subgroup.zpowers t) : Subgroup G) : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent, commutator_zpowers_eq_closure_Kapp htX, sup_comm] at hmap
  exact hmap

/-! ## App. I (4) -/

theorem appI_four {G : Type*} [Group G] [Finite G] {d : ℕ} (hd : d.Prime) {t : G}
    (ht : orderOf t = d) {X : Subgroup G} (htX : Work.NormalComplement.NormalizedBy t X)
    (hdX : Nat.Coprime (Nat.card X) d) :
    Work.NormalComplement.Kapp t X ⊆ (X : Set G) ∧
    (∀ k ∈ Work.NormalComplement.Kapp t X, ∀ v ∈ Subgroup.centralizer ({t} : Set G) ⊓ X,
      v * k * v⁻¹ ∈ Work.NormalComplement.Kapp t X) ∧
    (∀ x ∈ X, ∀ k ∈ Subgroup.closure (Work.NormalComplement.Kapp t X),
      x * k * x⁻¹ ∈ Subgroup.closure (Work.NormalComplement.Kapp t X)) ∧
    Subgroup.closure (Work.NormalComplement.Kapp t X) ⊔
      (Subgroup.centralizer ({t} : Set G) ⊓ X) = X ∧
    (∀ k ∈ Subgroup.closure (Work.NormalComplement.Kapp t X),
      t * k * t⁻¹ ∈ Subgroup.closure (Work.NormalComplement.Kapp t X)) ∧
    Work.NormalComplement.Kapp t (Subgroup.closure (Work.NormalComplement.Kapp t X)) =
      Work.NormalComplement.Kapp t X ∧
    Nat.card ↥(Subgroup.closure (Work.NormalComplement.Kapp t X)) =
      (Work.NormalComplement.Kapp t X).ncard *
        Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X ⊓
          Subgroup.closure (Work.NormalComplement.Kapp t X)) := by
  have hKX : Subgroup.closure (Kapp t X) ≤ X := (Subgroup.closure_le X).mpr (Kapp_subset htX)
  have hsup : Subgroup.closure (Kapp t X) ⊔ (Subgroup.centralizer ({t} : Set G) ⊓ X) = X :=
    closure_Kapp_sup_centralizer_aux hd ht htX hdX
  have hnormal : X ≤ Subgroup.normalizer ((Subgroup.closure (Kapp t X)) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    exact Kapp_conj_normal' h hh k hk
  have h6 : Kapp t (Subgroup.closure (Kapp t X)) = Kapp t X := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨y, hy, rfl⟩
      exact ⟨y, hKX hy, rfl⟩
    · rintro z ⟨y, hyX, rfl⟩
      have hVnK : Subgroup.centralizer ({t} : Set G) ⊓ X ≤
          Subgroup.normalizer ((Subgroup.closure (Kapp t X)) : Set G) :=
        le_trans inf_le_right hnormal
      have hyVK : y ∈ (Subgroup.centralizer ({t} : Set G) ⊓ X) *
          (Subgroup.closure (Kapp t X) : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVnK, sup_comm, hsup]
        exact hyX
      rw [Set.mem_mul] at hyVK
      obtain ⟨v, hv, k, hk, hvk⟩ := hyVK
      have hvt : t * v = v * t := (Subgroup.mem_centralizer_iff.mp hv.1) t (Set.mem_singleton t)
      have hv1 : v⁻¹ * t * v = t := by
        calc v⁻¹ * t * v = v⁻¹ * (t * v) := by group
          _ = v⁻¹ * (v * t) := by rw [hvt]
          _ = t := by group
      rw [← hvk]
      have heq : t⁻¹ * (v * k)⁻¹ * t * (v * k) = t⁻¹ * k⁻¹ * t * k := by
        rw [mul_inv_rev]
        calc t⁻¹ * (k⁻¹ * v⁻¹) * t * (v * k)
            = t⁻¹ * k⁻¹ * (v⁻¹ * t * v) * k := by group
          _ = t⁻¹ * k⁻¹ * t * k := by rw [hv1]
      rw [heq]
      exact ⟨k, hk, rfl⟩
  refine ⟨Kapp_subset htX, ?_, ?_, hsup, ?_, h6, ?_⟩
  · intro k hk v hv
    exact Kapp_conj_centralizer k hk v hv
  · intro x hx k hk
    exact Kapp_conj_normal' x hx k hk
  · intro k hk
    exact t_normalizes_K htX k hk
  · have hsub : Nat.card ↥((Subgroup.centralizer ({t} : Set G) ⊓
          Subgroup.closure (Kapp t X)).subgroupOf (Subgroup.closure (Kapp t X)))
        = Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.closure (Kapp t X)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : Subgroup.centralizer ({t} : Set G) ⊓
          Subgroup.closure (Kapp t X) ≤ Subgroup.closure (Kapp t X))).toEquiv
    have hinf : Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ Subgroup.closure (Kapp t X)
        = Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.closure (Kapp t X) := by
      refine le_antisymm ?_ ?_
      · intro x hx; exact ⟨hx.1.1, hx.2⟩
      · intro x hx; exact ⟨⟨hx.1, hKX hx.2⟩, hx.2⟩
    calc Nat.card ↥(Subgroup.closure (Kapp t X))
        = Nat.card ↥((Subgroup.centralizer ({t} : Set G) ⊓
              Subgroup.closure (Kapp t X)).subgroupOf (Subgroup.closure (Kapp t X)))
            * ((Subgroup.centralizer ({t} : Set G) ⊓
              Subgroup.closure (Kapp t X)).subgroupOf (Subgroup.closure (Kapp t X))).index :=
          (Subgroup.card_mul_index _).symm
      _ = Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.closure (Kapp t X))
            * ((Subgroup.centralizer ({t} : Set G) ⊓
              Subgroup.closure (Kapp t X)).subgroupOf (Subgroup.closure (Kapp t X))).index := by
          rw [hsub]
      _ = Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.closure (Kapp t X))
            * (Kapp t (Subgroup.closure (Kapp t X))).ncard := by
          rw [← appI_kapp_ncard t (Subgroup.closure (Kapp t X))]
      _ = Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.closure (Kapp t X))
            * (Kapp t X).ncard := by rw [h6]
      _ = Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X ⊓ Subgroup.closure (Kapp t X))
            * (Kapp t X).ncard := by rw [← hinf]
      _ = (Kapp t X).ncard
            * Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ X ⊓
              Subgroup.closure (Kapp t X)) := Nat.mul_comm _ _

end Work.NormalComplement
