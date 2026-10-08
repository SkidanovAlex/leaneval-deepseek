import Mathlib
import Submission.Work.Hering.AppVIII.CTwoStepDefs
import Submission.Work.Hering.AppVIII.CTwoStepFacts
import Submission.Work.Hering.AppVIII.Defs
import Submission.Work.Hering.AppVIII.PolarDefs
import Submission.Work.Hering.AppVIII.isotropic_unique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVIII

open Work.Higman

set_option autoImplicit false

/-- `W = {u | u.1 = 0}` is in bijection with `K` via the second coordinate. -/
noncomputable def wsubEquiv : Wsub ≃ KC 1 where
  toFun u := (u : KC 1 × KC 1).2
  invFun y := ⟨(0, y), rfl⟩
  left_inv := by
    rintro ⟨⟨x, y⟩, hx⟩
    simp only [mem_Wsub] at hx
    subst hx
    exact Subtype.ext rfl
  right_inv := by intro y; rfl

theorem cTypeP1_top (ε : Work.Hering.AppVIII.KC 1)
    (haniso : ∀ x y : Work.Hering.AppVIII.KC 1,
      x * (Work.Hering.AppVIII.thetaC 1 x) +
        ε * (Work.Higman.sqrtF (Work.Hering.AppVIII.KC 1) x *
          Work.Hering.AppVIII.thetaC 1 (y * y)) + y * y = 0 →
        x = 0 ∧ y = 0) :
    ∀ α : MulAut (Work.Hering.AppVIII.CTypeC 1 ε),
      α ∈ Work.Hering.stabilizerMulAut (Work.Hering.AppVIII.P1C 1 ε) := by
  have hε : ε ≠ 0 := by
    rintro rfl
    have h1 : (1 : KC 1) * thetaC 1 (1 : KC 1) +
        (0 : KC 1) * (sqrtF (KC 1) 1 * thetaC 1 (1 * 1)) + 1 * 1 = 0 := by
      simp only [map_one, mul_one, zero_mul, one_mul, add_zero, CharTwo.add_self_eq_zero]
    exact one_ne_zero (haniso 1 1 h1).1
  intro α
  have hkey : ∀ u : KC 1 × KC 1, (fstFun α u).1 = 0 ↔ u.1 = 0 := by
    let f : (KC 1 × KC 1) →+ (KC 1 × KC 1) :=
      { toFun := fstFun α
        map_zero' := by
          show (α (⟨(0 : KC 1 × KC 1), (0 : KC 1)⟩ : CTypeC 1 ε)).fst = 0
          simp [show (⟨(0 : KC 1 × KC 1), (0 : KC 1)⟩ : CTypeC 1 ε) = 1 from rfl]
        map_add' := fstFun_add hε α }
    have hsnd0 : sndFun α (0 : KC 1) = 0 := by
      have h := sndFun_add hε α (0 : KC 1) (0 : KC 1)
      simpa using h
    have hβ : ∀ u v : KC 1 × KC 1,
        betaP ε (f u) (f v) = sndFun α (betaP ε u v) := by
      intro u v
      have h1 : betaP ε (f u) (f v) =
          quadC 1 ε (f u + f v) + quadC 1 ε (f u) + quadC 1 ε (f v) :=
        (quadC_polar ε (f u) (f v)).symm
      have h2 : sndFun α (betaP ε u v) =
          sndFun α (quadC 1 ε (u + v) + quadC 1 ε u + quadC 1 ε v) := by
        rw [quadC_polar]
      rw [h1, h2, show f u + f v = f (u + v) from (map_add f u v).symm]
      rw [sndFun_add hε α (quadC 1 ε (u + v) + quadC 1 ε u) (quadC 1 ε v),
        sndFun_add hε α (quadC 1 ε (u + v)) (quadC 1 ε u)]
      rw [sndFun_quadC α (u + v), sndFun_quadC α u, sndFun_quadC α v]
      rfl
    have hcardW : Nat.card Wsub = 8 := by
      rw [Nat.card_congr wsubEquiv, GaloisField.card 2 3 (by norm_num)]
      norm_num
    have hcard : Nat.card (Wsub.map f) = 8 := by
      rw [AddSubgroup.card_map_of_injective (K := Wsub) (f := f)
        (show Function.Injective f from (fstFun_bijective hε α).1)]
      exact hcardW
    have hiso : ∀ u ∈ Wsub.map f, ∀ v ∈ Wsub.map f, betaP ε u v = 0 := by
      intro u hu v hv
      rw [AddSubgroup.mem_map] at hu hv
      obtain ⟨w, hw, rfl⟩ := hu
      obtain ⟨w', hw', rfl⟩ := hv
      rw [hβ w w', show betaP ε w w' = 0 from betaP_Wsub ε ⟨w, hw⟩ ⟨w', hw'⟩, hsnd0]
    have hU : ∀ u ∈ Wsub.map f, u.1 = 0 := isotropic_unique ε hε _ hcard hiso
    have hle : Wsub.map f ≤ Wsub := fun u hu => hU u hu
    intro u
    constructor
    · intro hu
      have hfu : f u ∈ Wsub := by
        show (f u).1 = 0
        simpa [f] using hu
      let g : Wsub → Wsub := fun w => ⟨f w, hle (AddSubgroup.mem_map_of_mem f w.2)⟩
      have hginj : Function.Injective g := by
        intro a b hab
        have h2 : f (a : KC 1 × KC 1) = f (b : KC 1 × KC 1) := congrArg Subtype.val hab
        exact Subtype.ext ((fstFun_bijective hε α).1 (by simpa [f] using h2))
      obtain ⟨w, hw⟩ := (Finite.surjective_of_injective hginj) ⟨f u, hfu⟩
      have hwu : (w : KC 1 × KC 1) = u := (fstFun_bijective hε α).1 (by
        have h := congrArg Subtype.val hw
        simpa [g, f] using h)
      rw [← hwu]; exact w.2
    · intro hu
      have hmem : f u ∈ Wsub.map f :=
        AddSubgroup.mem_map_of_mem f (by simpa [mem_Wsub] using hu)
      simpa [f] using hU (f u) hmem
  intro x
  change (α x).fst.1 = 0 ↔ x.fst.1 = 0
  rw [fst_alpha_eq hε α x]
  exact hkey x.fst

end Work.Hering.AppVIII
