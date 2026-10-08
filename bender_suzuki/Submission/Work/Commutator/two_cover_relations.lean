import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.HS.hard_two_cover
import Submission.Work.Higman.RedAux.setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.Commutator

open scoped commutatorElement

/-! ## Auxiliary group-theoretic lemmas

In the `C₄` configuration of Higman's classification of Suzuki 2-groups the two covers
`C, E` of the maximal `ξ`-invariant abelian normal subgroup `A` satisfy a small list of
"two-cover relations".  This file collects them.

We isolate three elementary lemmas.
-/

/-- **Commutator diagonal identity.**  If `x ^ 2` and `y ^ 2` are central then the commutator
`c = x * y * x⁻¹ * y⁻¹` is inverted by conjugation by `x` and by `y`; equivalently
`⁅c, x⁆ = c ^ 2 = ⁅c, y⁆`. -/
theorem commutator_diag_relations {G : Type} [Group G] (x y : G)
    (hx2 : x ^ 2 ∈ Subgroup.center G) (hy2 : y ^ 2 ∈ Subgroup.center G) :
    ((x * y * x⁻¹ * y⁻¹) * x * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ 2) ∧
    ((x * y * x⁻¹ * y⁻¹) * y * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ 2) := by
  have hx2' : x * x ∈ Subgroup.center G := by simpa only [pow_two] using hx2
  have hy2' : y * y ∈ Subgroup.center G := by simpa only [pow_two] using hy2
  have inv_conj : ∀ z w : G, w * z * w⁻¹ = z⁻¹ → w * z⁻¹ * w⁻¹ = z := by
    intro z w h
    have h' := congrArg Inv.inv h
    simp only [mul_inv_rev, inv_inv] at h'
    simpa only [mul_assoc] using h'
  have hxc : x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
    have hc : (x * x) * y = y * (x * x) := (Subgroup.mem_center_iff.mp hx2' y).symm
    rw [show (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ by group]
    calc x * (x * y * x⁻¹ * y⁻¹) * x⁻¹
        = (x * x) * y * (x⁻¹ * y⁻¹ * x⁻¹) := by group
      _ = y * (x * x) * (x⁻¹ * y⁻¹ * x⁻¹) := by rw [hc]
      _ = y * x * y⁻¹ * x⁻¹ := by group
  have hyc : y * (x * y * x⁻¹ * y⁻¹) * y⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
    have hc : x⁻¹ * (y * y)⁻¹ = (y * y)⁻¹ * x⁻¹ :=
      Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hy2') x⁻¹
    rw [show (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ by group]
    calc y * (x * y * x⁻¹ * y⁻¹) * y⁻¹
        = y * x * y * (x⁻¹ * (y * y)⁻¹) := by group
      _ = y * x * y * ((y * y)⁻¹ * x⁻¹) := by rw [hc]
      _ = y * x * y⁻¹ * x⁻¹ := by group
  have hxc' : x * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹ = x * y * x⁻¹ * y⁻¹ :=
    inv_conj _ _ hxc
  have hyc' : y * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ :=
    inv_conj _ _ hyc
  constructor
  · calc (x * y * x⁻¹ * y⁻¹) * x * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹
        = (x * y * x⁻¹ * y⁻¹) * (x * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹) := by group
      _ = (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by rw [hxc']
      _ = (x * y * x⁻¹ * y⁻¹) ^ 2 := (pow_two _).symm
  · calc (x * y * x⁻¹ * y⁻¹) * y * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹
        = (x * y * x⁻¹ * y⁻¹) * (y * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹) := by group
      _ = (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by rw [hyc']
      _ = (x * y * x⁻¹ * y⁻¹) ^ 2 := (pow_two _).symm

/-- The set of `y` with `⁅c, y⁆ ∈ N` is a subgroup; hence if it contains the generating
subgroups `C` and `E` of `C ⊔ E = ⊤` it is everything. -/
theorem comm_le_powSub_two_of_sup {P : Type} [Group P] {A C E : Subgroup P}
    [hCn : C.Normal] (hCEsup : C ⊔ E = ⊤) {c : P}
    (hB : (Work.Higman.powSub A 2).Normal)
    (hC : ∀ y ∈ C, c * y * c⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2)
    (hE : ∀ y ∈ E, c * y * c⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2) :
    ∀ y : P, c * y * c⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2 := by
  let N : Subgroup P := Work.Higman.powSub A 2
  have hN : N.Normal := hB
  let K : Subgroup P :=
    { carrier := {y : P | c * y * c⁻¹ * y⁻¹ ∈ N}
      mul_mem' := by
        intro y₁ y₂ h1 h2
        change c * (y₁ * y₂) * c⁻¹ * (y₁ * y₂)⁻¹ ∈ N
        have h2' : c * y₂ * c⁻¹ * y₂⁻¹ ∈ N := h2
        rw [show c * (y₁ * y₂) * c⁻¹ * (y₁ * y₂)⁻¹
              = (c * y₁ * c⁻¹ * y₁⁻¹) * (y₁ * (c * y₂ * c⁻¹ * y₂⁻¹) * y₁⁻¹) by group]
        exact N.mul_mem h1 (hN.conj_mem _ h2' y₁)
      one_mem' := by simp
      inv_mem' := by
        intro y h1
        change c * y⁻¹ * c⁻¹ * (y⁻¹)⁻¹ ∈ N
        have h0 : c * (y * y⁻¹) * c⁻¹ * (y * y⁻¹)⁻¹ ∈ N := by simp
        rw [show c * (y * y⁻¹) * c⁻¹ * (y * y⁻¹)⁻¹
              = (c * y * c⁻¹ * y⁻¹) * (y * (c * y⁻¹ * c⁻¹ * (y⁻¹)⁻¹) * y⁻¹) by group] at h0
        have h2 : y * (c * y⁻¹ * c⁻¹ * (y⁻¹)⁻¹) * y⁻¹ ∈ N := by
          have h1' : (c * y * c⁻¹ * y⁻¹)⁻¹ ∈ N := N.inv_mem h1
          have h3 := N.mul_mem h1' h0
          rwa [show (c * y * c⁻¹ * y⁻¹)⁻¹
                * ((c * y * c⁻¹ * y⁻¹) * (y * (c * y⁻¹ * c⁻¹ * (y⁻¹)⁻¹) * y⁻¹))
                = y * (c * y⁻¹ * c⁻¹ * (y⁻¹)⁻¹) * y⁻¹ by group] at h3
        have h4 : y⁻¹ * (y * (c * y⁻¹ * c⁻¹ * (y⁻¹)⁻¹) * y⁻¹) * (y⁻¹)⁻¹ ∈ N :=
          hN.conj_mem _ h2 y⁻¹
        rwa [show y⁻¹ * (y * (c * y⁻¹ * c⁻¹ * (y⁻¹)⁻¹) * y⁻¹) * (y⁻¹)⁻¹
              = c * y⁻¹ * c⁻¹ * (y⁻¹)⁻¹ by group] at h4 }
  have hCK : C ≤ K := fun y hy => hC y hy
  have hEK : E ≤ K := fun y hy => hE y hy
  have htop : (⊤ : Subgroup P) ≤ K := by
    rw [← hCEsup]; exact sup_le hCK hEK
  exact fun y => htop (Subgroup.mem_top y)

/-- **One half of the two-cover relation.**  In the `C₄` configuration, if `S` is a
`ξ`-invariant normal minimal cover of `A` and `T` is the complementary cover with
`S ⊔ T = ⊤`, then every `s ∈ S \ A` has a commutator with some `t ∈ T` that misses `A ^ (2)`.

The hypothesis list is exactly the part of the two-cover configuration used by the argument:
`⁅S,S⁆ = A²`, `⁅S,A⁆ = A²`, `C_S(A) = A` (through the cover property), `S ⊔ T = ⊤`,
`⁅T,T⁆ = A²`. -/
theorem one_sided_not_mem {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A S T : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hSn : S.Normal) (hSinv : S.map (h.xi : MulAut P).toMonoidHom = S)
    (hAS : A ≤ S)
    (hScover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ S → D = A ∨ D = S)
    (hSd : ⁅S, S⁆ = Work.Higman.powSub A 2)
    (hSAd : ⁅S, A⁆ = Work.Higman.powSub A 2)
    (hSTsup : S ⊔ T = ⊤)
    (hTd : ⁅T, T⁆ = Work.Higman.powSub A 2) :
    ∀ s ∈ S, s ∉ A → ∃ t ∈ T, s * t * s⁻¹ * t⁻¹ ∉ Work.Higman.powSub A 2 := by
  haveI : A.Normal := hA.normal
  haveI : S.Normal := hSn
  have hB : (Work.Higman.powSub A 2).Normal := Work.Higman.powSub_normal hA.normal 2
  intro s hs hsA
  by_contra hcon
  push_neg at hcon
  -- `s` centralises `P` modulo `A ^ (2)`
  have hsErad : s ∈ Work.Higman.HS.Erad h A := by
    rw [Work.Higman.HS.mem_Erad_iff]
    intro y
    have hS' : ∀ y ∈ S, s * y * s⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2 := by
      intro y hy
      have h1 := Subgroup.commutator_mem_commutator hs hy
      rw [hSd] at h1
      simpa [commutatorElement_def] using h1
    exact comm_le_powSub_two_of_sup (A := A) (C := S) (E := T) hSTsup hB hS' hcon y
  -- the subgroup `S ⊓ Erad` is a normal `ξ`-invariant cover of `A` inside `S`
  set D : Subgroup P := S ⊓ Work.Higman.HS.Erad h A with hDdef
  have hAErad : A ≤ Work.Higman.HS.Erad h A :=
    Work.Higman.HS.A_le_Erad (h := h) (A := A) (C := S) hA.abelian hA.map_eq hNA htop hA4 hSAd
  have hAD : A ≤ D := fun x hx => ⟨hAS hx, hAErad hx⟩
  have hDleS : D ≤ S := inf_le_left
  have hsD : s ∈ D := ⟨hs, hsErad⟩
  have hDnorm : D.Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    have h1 : ⁅g, n⁆ ∈ A := by
      rw [← hGs]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n)
    rw [show g * n * g⁻¹ = ⁅g, n⁆ * n from by rw [commutatorElement_def]; group]
    exact D.mul_mem (hAD h1) hn
  have hDinv : D.map (h.xi : MulAut P).toMonoidHom = D := by
    rw [hDdef, Subgroup.map_inf _ _ _ (h.xi : MulAut P).injective, hSinv,
      Work.Higman.HS.map_xi_Erad (h := h) (A := A) hA.map_eq]
  rcases hScover D hDnorm hDinv hAD hDleS with hDA | hDS
  · exact hsA (hDA ▸ hsD)
  · -- then `S` centralises `P` modulo `A²`, so `⁅⊤,⊤⁆ ≤ A²`
    have hSErad : S ≤ Work.Higman.HS.Erad h A := hDS ▸ inf_le_right
    have hTErad : T ≤ Work.Higman.HS.Erad h A := by
      intro t ht
      rw [Work.Higman.HS.mem_Erad_iff]
      intro y
      have hT' : ∀ y ∈ T, t * y * t⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2 := by
        intro y hy
        have h1 := Subgroup.commutator_mem_commutator ht hy
        rw [hTd] at h1
        simpa [commutatorElement_def] using h1
      have hS'' : ∀ y ∈ S, t * y * t⁻¹ * y⁻¹ ∈ Work.Higman.powSub A 2 := by
        intro y hy
        have hyE := hSErad hy
        rw [Work.Higman.HS.mem_Erad_iff] at hyE
        have h1 := (Work.Higman.powSub A 2).inv_mem (hyE t)
        rwa [show (y * t * y⁻¹ * t⁻¹)⁻¹ = t * y * t⁻¹ * y⁻¹ by group] at h1
      exact comm_le_powSub_two_of_sup (A := A) (C := S) (E := T) hSTsup hB hS'' hT' y
    have hle : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.powSub A 2 :=
      Work.Higman.HS.commutator_le_powSub_two_of_sup (h := h) (A := A) (C := S) (E := T)
        hSTsup (le_of_eq hSd) hTErad
    have hAle2 : A ≤ Work.Higman.powSub A 2 := hGs ▸ hle
    exact (Work.Higman.RedAux.ne_powSub_two_of_card h htop hcard)
      (le_antisymm hAle2 (Work.Higman.powSub_le (by norm_num)))

/-- **Two-cover relations.**  In the `C₄` configuration of Higman's classification of
Suzuki 2-groups, the two complementary `ξ`-invariant normal covers `C, E` of the maximal
`ξ`-invariant abelian normal subgroup `A` satisfy:

* `⁅A,⊤⁆ = A ^ (2)`;
* each `c ∈ C \ A` has a commutator with some `e ∈ E` outside `A ^ (2)` (and symmetrically);
* for `c ∈ C`, `e ∈ E`, the commutator `c * e * c⁻¹ * e⁻¹` is inverted by conjugation by
  `c` and by `e`, i.e. `⁅⁅c,e⁆, c⁆ = ⁅c,e⁆ ^ 2 = ⁅⁅c,e⁆, e⁆`. -/
theorem two_cover_relations {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C E : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hEn : E.Normal)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hEinv : E.map (h.xi : MulAut P).toMonoidHom = E)
    (hAC : A ≤ C) (hAE : A ≤ E)
    (hCcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hEcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ E → D = A ∨ D = E)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) (hEd : ⁅E, E⁆ = Work.Higman.powSub A 2)
    (hCpow2 : Work.Higman.powSub C 2 = Work.Higman.powSub A 2)
    (hEpow2 : Work.Higman.powSub E 2 = Work.Higman.powSub A 2)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2) (hEAd : ⁅E, A⁆ = Work.Higman.powSub A 2)
    (hCE : C ⊓ E = A) (hCEsup : C ⊔ E = ⊤) :
    (⁅(A : Subgroup P), (⊤ : Subgroup P)⁆ = Work.Higman.powSub A 2) ∧
    (∀ c ∈ C, c ∉ A → ∃ e ∈ E, c * e * c⁻¹ * e⁻¹ ∉ Work.Higman.powSub A 2) ∧
    (∀ e ∈ E, e ∉ A → ∃ c ∈ C, c * e * c⁻¹ * e⁻¹ ∉ Work.Higman.powSub A 2) ∧
    (∀ c ∈ C, ∀ e ∈ E,
      ((c * e * c⁻¹ * e⁻¹) * c * (c * e * c⁻¹ * e⁻¹)⁻¹ * c⁻¹) = (c * e * c⁻¹ * e⁻¹) ^ 2) ∧
    (∀ c ∈ C, ∀ e ∈ E,
      ((c * e * c⁻¹ * e⁻¹) * e * (c * e * c⁻¹ * e⁻¹)⁻¹ * e⁻¹) = (c * e * c⁻¹ * e⁻¹) ^ 2) := by
  haveI : A.Normal := hA.normal
  have hcent : Work.Higman.powSub A 2 ≤ Subgroup.center P := by
    rw [htop]; exact h.omega1_le_center
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Work.Higman.HS.comm_A_top_eq_aux (h := h) (A := A) (C := C)
      hA.abelian hA.map_eq hNA htop hA4 hCAd
  · exact one_sided_not_mem (h := h) (A := A) (S := C) (T := E)
      hA hNA hGs htop hA4 hcard hCn hCinv hAC hCcover hCd hCAd hCEsup hEd
  · intro e he heA
    have hsup' : E ⊔ C = ⊤ := by rw [sup_comm]; exact hCEsup
    obtain ⟨c, hc, hce⟩ := one_sided_not_mem (h := h) (A := A) (S := E) (T := C)
      hA hNA hGs htop hA4 hcard hEn hEinv hAE hEcover hEd hEAd hsup' hCd e he heA
    refine ⟨c, hc, fun hcontra => hce ?_⟩
    rw [show e * c * e⁻¹ * c⁻¹ = (c * e * c⁻¹ * e⁻¹)⁻¹ by group]
    exact (Work.Higman.powSub A 2).inv_mem hcontra
  · intro c hc e he
    have hc2 : c ^ 2 ∈ Subgroup.center P := hcent (hCpow2 ▸ Work.Higman.pow_mem_powSub (A := C) hc)
    have he2 : e ^ 2 ∈ Subgroup.center P := hcent (hEpow2 ▸ Work.Higman.pow_mem_powSub (A := E) he)
    exact (commutator_diag_relations c e hc2 he2).1
  · intro c hc e he
    have hc2 : c ^ 2 ∈ Subgroup.center P := hcent (hCpow2 ▸ Work.Higman.pow_mem_powSub (A := C) hc)
    have he2 : e ^ 2 ∈ Subgroup.center P := hcent (hEpow2 ▸ Work.Higman.pow_mem_powSub (A := E) he)
    exact (commutator_diag_relations c e hc2 he2).2

end Work.Commutator
