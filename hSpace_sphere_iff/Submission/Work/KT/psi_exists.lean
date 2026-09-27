import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.Nat
import Submission.Work.KT.Psi.sq2Part_idem
import Submission.Work.KT.Psi.sq2Part_MvN
import Submission.Work.KT.Psi.sq2Part_split
import Submission.Work.KT.Psi.psi2Cls_sum
import Submission.Work.KT.Psi.psi2Cls_kron
import Submission.Work.KT.Psi.cubePart_idem
import Submission.Work.KT.Psi.cubePart_MvN
import Submission.Work.KT.Psi.cubePart_conj
import Submission.Work.KT.Psi.psi3Cls_sum
import Submission.Work.KT.Psi.psi3Cls_kron
import Submission.Work.KT.Psi.mulCls_comm

/-! The Adams operations `ψ²`, `ψ³` on `K₀` of a commutative `ℂ`-algebra.  The generator-level
truth of `ψ²p = [Sym²p] − [Λ²p]`, `ψ³p = [V₁p] − [V_ωp]` (additivity, `MvN`-invariance,
naturality, multiplicativity, `ψ²x ≡ x² (mod 2)`) is proved in the modules under
`Submission/Work/KT/Psi/`; this file assembles them into the node statement. -/

namespace Work.KT

open Matrix

noncomputable section

variable {A B : Type}

/-! ## `MvN`-invariance of `psi2Cls`, `psi3Cls` -/

theorem psi2Cls_MvN [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) (h : p.MvN q) :
    psi2Cls p = psi2Cls q := by
  unfold psi2Cls
  rw [if_pos hp, if_pos hq, Psi.sq2Part_MvN hA 1 hp hq h, Psi.sq2Part_MvN hA (-1) hp hq h]

theorem psi3Cls_MvN [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p q : Mat A} (hp : p.IsIdem) (hq : q.IsIdem) (h : p.MvN q) :
    psi3Cls p = psi3Cls q := by
  unfold psi3Cls
  rw [if_pos hp, if_pos hq, Psi.cubePart_MvN hA 1 (by norm_num) hp hq h,
    Psi.cubePart_MvN hA omega omega_pow_three hp hq h]

/-! ## Existence of `ψ²`, `ψ³` -/

theorem psi2_exists [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x) :
    ∃ ψ : K0 A →+ K0 A, IsPsi2 ψ := by
  have hker : K0Rel A ≤ (FreeAbelianGroup.lift (fun p : Mat A => psi2Cls p)).ker := by
    unfold K0Rel
    rw [AddSubgroup.closure_le]
    rintro x ((⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, h, rfl⟩) | ⟨p, hp, rfl⟩)
    · show (FreeAbelianGroup.lift (fun p : Mat A => psi2Cls p))
          (FreeAbelianGroup.of (p.sum q) - FreeAbelianGroup.of p - FreeAbelianGroup.of q) = 0
      rw [map_sub, map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
        FreeAbelianGroup.lift_apply_of, Psi.psi2Cls_sum hA hp hq]
      abel
    · show (FreeAbelianGroup.lift (fun p : Mat A => psi2Cls p))
          (FreeAbelianGroup.of p - FreeAbelianGroup.of q) = 0
      rw [map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
        psi2Cls_MvN hA hp hq h]
      abel
    · show (FreeAbelianGroup.lift (fun p : Mat A => psi2Cls p)) (FreeAbelianGroup.of p) = 0
      rw [FreeAbelianGroup.lift_apply_of,
        show psi2Cls p = 0 from by unfold psi2Cls; rw [if_neg hp]]
  exact ⟨QuotientAddGroup.lift (K0Rel A) (FreeAbelianGroup.lift (fun p : Mat A => psi2Cls p))
    hker, fun p => by
      show QuotientAddGroup.lift (K0Rel A) (FreeAbelianGroup.lift (fun p : Mat A => psi2Cls p))
        hker (cls p) = psi2Cls p
      rw [show cls p = (QuotientAddGroup.mk (FreeAbelianGroup.of p) : K0 A) from rfl,
        QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]⟩

theorem psi3_exists [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x) :
    ∃ ψ : K0 A →+ K0 A, IsPsi3 ψ := by
  have hker : K0Rel A ≤ (FreeAbelianGroup.lift (fun p : Mat A => psi3Cls p)).ker := by
    unfold K0Rel
    rw [AddSubgroup.closure_le]
    rintro x ((⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, h, rfl⟩) | ⟨p, hp, rfl⟩)
    · show (FreeAbelianGroup.lift (fun p : Mat A => psi3Cls p))
          (FreeAbelianGroup.of (p.sum q) - FreeAbelianGroup.of p - FreeAbelianGroup.of q) = 0
      rw [map_sub, map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
        FreeAbelianGroup.lift_apply_of, Psi.psi3Cls_sum hA hp hq]
      abel
    · show (FreeAbelianGroup.lift (fun p : Mat A => psi3Cls p))
          (FreeAbelianGroup.of p - FreeAbelianGroup.of q) = 0
      rw [map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
        psi3Cls_MvN hA hp hq h]
      abel
    · show (FreeAbelianGroup.lift (fun p : Mat A => psi3Cls p)) (FreeAbelianGroup.of p) = 0
      rw [FreeAbelianGroup.lift_apply_of,
        show psi3Cls p = 0 from by unfold psi3Cls; rw [if_neg hp]]
  exact ⟨QuotientAddGroup.lift (K0Rel A) (FreeAbelianGroup.lift (fun p : Mat A => psi3Cls p))
    hker, fun p => by
      show QuotientAddGroup.lift (K0Rel A) (FreeAbelianGroup.lift (fun p : Mat A => psi3Cls p))
        hker (cls p) = psi3Cls p
      rw [show cls p = (QuotientAddGroup.mk (FreeAbelianGroup.of p) : K0 A) from rfl,
        QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]⟩

/-! ## Naturality -/

theorem map_cls_sq2 [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (hA : ∀ x y : A, x * y = y * x) (ε : ℂ) (hε : ε * ε = 1) {p : Mat A} (hp : p.IsIdem) :
    K0.mapA φ (cls (sq2Part ε p)) = cls (sq2Part ε (p.map φ.toRingHom)) := by
  rw [map_cls_uncond]
  unfold mapCls
  rw [if_pos (Psi.sq2Part_idem hA ε hε hp), sq2Part_map]

theorem map_cls_cube [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (hA : ∀ x y : A, x * y = y * x) (lam : ℂ) (hlam : lam ^ 3 = 1) {p : Mat A}
    (hp : p.IsIdem) :
    K0.mapA φ (cls (cubePart lam p)) = cls (cubePart lam (p.map φ.toRingHom)) := by
  rw [map_cls_uncond]
  unfold mapCls
  rw [if_pos (Psi.cubePart_idem hA lam hlam hp), cubePart_map]

theorem psi2_nat [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (hA : ∀ x y : A, x * y = y * x) (ψA : K0 A →+ K0 A) (ψB : K0 B →+ K0 B)
    (hA' : IsPsi2 ψA) (hB' : IsPsi2 ψB) :
    ∀ x, K0.mapA φ (ψA x) = ψB (K0.mapA φ x) := by
  have key : (K0.mapA φ).comp ψA = ψB.comp (K0.mapA φ) :=
    addHom_ext_cls (fun p => ?_)
  · intro x
    exact congrArg (fun f : K0 A →+ K0 B => f x) key
  show K0.mapA φ (ψA (cls p)) = ψB (K0.mapA φ (cls p))
  rw [hA' p, show K0.mapA φ (cls p) = mapCls φ.toRingHom p from map_cls_uncond φ.toRingHom p]
  by_cases hp : p.IsIdem
  · rw [show mapCls φ.toRingHom p = cls (p.map φ.toRingHom) from by
        unfold mapCls; rw [if_pos hp],
      hB' (p.map φ.toRingHom),
      show psi2Cls p = cls (sq2Part 1 p) - cls (sq2Part (-1) p) from by
        unfold psi2Cls; rw [if_pos hp],
      show psi2Cls (p.map φ.toRingHom) = cls (sq2Part 1 (p.map φ.toRingHom)) -
          cls (sq2Part (-1) (p.map φ.toRingHom)) from by
        unfold psi2Cls; rw [if_pos (Mat.isIdem_map hp φ.toRingHom)],
      map_sub, map_cls_sq2 φ hA 1 (by norm_num) hp, map_cls_sq2 φ hA (-1) (by norm_num) hp]
  · rw [show mapCls φ.toRingHom p = 0 from by unfold mapCls; rw [if_neg hp], map_zero,
      show psi2Cls p = 0 from by unfold psi2Cls; rw [if_neg hp], map_zero]

theorem psi3_nat [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (hA : ∀ x y : A, x * y = y * x) (ψA : K0 A →+ K0 A) (ψB : K0 B →+ K0 B)
    (hA' : IsPsi3 ψA) (hB' : IsPsi3 ψB) :
    ∀ x, K0.mapA φ (ψA x) = ψB (K0.mapA φ x) := by
  have key : (K0.mapA φ).comp ψA = ψB.comp (K0.mapA φ) :=
    addHom_ext_cls (fun p => ?_)
  · intro x
    exact congrArg (fun f : K0 A →+ K0 B => f x) key
  show K0.mapA φ (ψA (cls p)) = ψB (K0.mapA φ (cls p))
  rw [hA' p, show K0.mapA φ (cls p) = mapCls φ.toRingHom p from map_cls_uncond φ.toRingHom p]
  by_cases hp : p.IsIdem
  · rw [show mapCls φ.toRingHom p = cls (p.map φ.toRingHom) from by
        unfold mapCls; rw [if_pos hp],
      hB' (p.map φ.toRingHom),
      show psi3Cls p = cls (cubePart 1 p) - cls (cubePart omega p) from by
        unfold psi3Cls; rw [if_pos hp],
      show psi3Cls (p.map φ.toRingHom) = cls (cubePart 1 (p.map φ.toRingHom)) -
          cls (cubePart omega (p.map φ.toRingHom)) from by
        unfold psi3Cls; rw [if_pos (Mat.isIdem_map hp φ.toRingHom)],
      map_sub, map_cls_cube φ hA 1 (by norm_num) hp,
      map_cls_cube φ hA omega omega_pow_three hp]
  · rw [show mapCls φ.toRingHom p = 0 from by unfold mapCls; rw [if_neg hp], map_zero,
      show psi3Cls p = 0 from by unfold psi3Cls; rw [if_neg hp], map_zero]

/-! ## Multiplicativity -/

theorem psi2_mul [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (μ : K0 A →+ K0 A →+ K0 A) (ψ2 : K0 A →+ K0 A) (hμ : IsK0Mul μ) (h2 : IsPsi2 ψ2) :
    ∀ x y, ψ2 (μ x y) = μ (ψ2 x) (ψ2 y) := by
  let F : K0 A →+ K0 A →+ K0 A := (AddMonoidHom.compHom ψ2).comp μ
  let G : K0 A →+ K0 A →+ K0 A :=
    { toFun := fun x => (μ (ψ2 x)).comp ψ2
      map_zero' := by ext y; simp
      map_add' := fun a b => by
        ext y
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply, map_add] }
  have h : F = G := addHom₂_ext_cls (F := F) (G := G) (fun p q => by
    show ψ2 (μ (cls p) (cls q)) = μ (ψ2 (cls p)) (ψ2 (cls q))
    rw [h2 p, h2 q]
    by_cases hp : p.IsIdem
    · by_cases hq : q.IsIdem
      · have hpq : μ (cls p) (cls q) = cls (p.kron q) := by
          rw [hμ]
          unfold mulCls
          rw [if_pos ⟨hp, hq⟩]
        have hSp : psi2Cls p = cls (sq2Part 1 p) - cls (sq2Part (-1) p) := by
          unfold psi2Cls; rw [if_pos hp]
        have hSq : psi2Cls q = cls (sq2Part 1 q) - cls (sq2Part (-1) q) := by
          unfold psi2Cls; rw [if_pos hq]
        rw [hpq, h2 (p.kron q), hSp, hSq,
          show μ (cls (sq2Part 1 p) - cls (sq2Part (-1) p))
                (cls (sq2Part 1 q) - cls (sq2Part (-1) q))
              = mulCls (sq2Part 1 p) (sq2Part 1 q) - mulCls (sq2Part 1 p) (sq2Part (-1) q)
                - mulCls (sq2Part (-1) p) (sq2Part 1 q)
                + mulCls (sq2Part (-1) p) (sq2Part (-1) q) from by
            simp only [map_sub, AddMonoidHom.sub_apply]
            rw [hμ, hμ, hμ, hμ]
            abel]
        exact Psi.psi2Cls_kron hA hp hq
      · have hpq : μ (cls p) (cls q) = 0 := by
          rw [hμ]; unfold mulCls; rw [if_neg (fun h => hq h.2)]
        rw [hpq, map_zero, show psi2Cls q = 0 from by unfold psi2Cls; rw [if_neg hq]]
        exact (map_zero (μ (psi2Cls p))).symm
    · have hpq : μ (cls p) (cls q) = 0 := by
        rw [hμ]; unfold mulCls; rw [if_neg (fun h => hp h.1)]
      rw [hpq, map_zero, show psi2Cls p = 0 from by unfold psi2Cls; rw [if_neg hp],
        map_zero μ, AddMonoidHom.zero_apply])
  intro x y
  exact congrArg (fun f : K0 A →+ K0 A →+ K0 A => f x y) h

theorem psi3_mul [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (μ : K0 A →+ K0 A →+ K0 A) (ψ3 : K0 A →+ K0 A) (hμ : IsK0Mul μ) (h3 : IsPsi3 ψ3) :
    ∀ x y, ψ3 (μ x y) = μ (ψ3 x) (ψ3 y) := by
  let F : K0 A →+ K0 A →+ K0 A := (AddMonoidHom.compHom ψ3).comp μ
  let G : K0 A →+ K0 A →+ K0 A :=
    { toFun := fun x => (μ (ψ3 x)).comp ψ3
      map_zero' := by ext y; simp
      map_add' := fun a b => by
        ext y
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply, map_add] }
  have h : F = G := addHom₂_ext_cls (F := F) (G := G) (fun p q => by
    show ψ3 (μ (cls p) (cls q)) = μ (ψ3 (cls p)) (ψ3 (cls q))
    rw [h3 p, h3 q]
    by_cases hp : p.IsIdem
    · by_cases hq : q.IsIdem
      · have hpq : μ (cls p) (cls q) = cls (p.kron q) := by
          rw [hμ]
          unfold mulCls
          rw [if_pos ⟨hp, hq⟩]
        have hSp : psi3Cls p = cls (cubePart 1 p) - cls (cubePart omega p) := by
          unfold psi3Cls; rw [if_pos hp]
        have hSq : psi3Cls q = cls (cubePart 1 q) - cls (cubePart omega q) := by
          unfold psi3Cls; rw [if_pos hq]
        rw [hpq, h3 (p.kron q), hSp, hSq,
          show μ (cls (cubePart 1 p) - cls (cubePart omega p))
                (cls (cubePart 1 q) - cls (cubePart omega q))
              = mulCls (cubePart 1 p) (cubePart 1 q) - mulCls (cubePart 1 p) (cubePart omega q)
                - mulCls (cubePart omega p) (cubePart 1 q)
                + mulCls (cubePart omega p) (cubePart omega q) from by
            simp only [map_sub, AddMonoidHom.sub_apply]
            rw [hμ, hμ, hμ, hμ]
            abel]
        exact Psi.psi3Cls_kron hA hp hq
      · have hpq : μ (cls p) (cls q) = 0 := by
          rw [hμ]; unfold mulCls; rw [if_neg (fun h => hq h.2)]
        rw [hpq, map_zero, show psi3Cls q = 0 from by unfold psi3Cls; rw [if_neg hq]]
        exact (map_zero (μ (psi3Cls p))).symm
    · have hpq : μ (cls p) (cls q) = 0 := by
        rw [hμ]; unfold mulCls; rw [if_neg (fun h => hp h.1)]
      rw [hpq, map_zero, show psi3Cls p = 0 from by unfold psi3Cls; rw [if_neg hp],
        map_zero μ, AddMonoidHom.zero_apply])
  intro x y
  exact congrArg (fun f : K0 A →+ K0 A →+ K0 A => f x y) h

/-! ## `ψ²x ≡ x² (mod 2)` -/

theorem psi2_mod_two [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (μ : K0 A →+ K0 A →+ K0 A) (ψ2 : K0 A →+ K0 A) (hμ : IsK0Mul μ) (h2 : IsPsi2 ψ2) :
    ∀ x : K0 A, ∃ y : K0 A, ψ2 x - μ x x = 2 • y := by
  have hcross : ∀ x y : K0 A, ∃ z, μ x y + μ y x = 2 • z := by
    have hgen : ∀ p q : Mat A, ∃ z, μ (cls p) (cls q) + μ (cls q) (cls p) = 2 • z := by
      intro p q
      by_cases hp : p.IsIdem
      · by_cases hq : q.IsIdem
        · refine ⟨cls (p.kron q), ?_⟩
          rw [hμ, hμ,
            show mulCls p q = cls (p.kron q) from by unfold mulCls; rw [if_pos ⟨hp, hq⟩],
            show mulCls q p = cls (p.kron q) from by
              rw [Psi.mulCls_comm hA q p]; unfold mulCls; rw [if_pos ⟨hp, hq⟩]]
          abel
        · refine ⟨0, ?_⟩
          rw [hμ, hμ,
            show mulCls p q = 0 from by unfold mulCls; rw [if_neg (fun h => hq h.2)],
            show mulCls q p = 0 from by unfold mulCls; rw [if_neg (fun h => hq h.1)]]
          simp
      · refine ⟨0, ?_⟩
        rw [hμ, hμ,
          show mulCls p q = 0 from by unfold mulCls; rw [if_neg (fun h => hp h.1)],
          show mulCls q p = 0 from by unfold mulCls; rw [if_neg (fun h => hp h.2)]]
        simp
    have hstep : ∀ p : Mat A, ∀ y : K0 A, ∃ z, μ (cls p) y + μ y (cls p) = 2 • z := by
      intro p y
      have hmem : y ∈ AddSubgroup.closure (Set.range (cls : Mat A → K0 A)) := by
        rw [cls_closure_top]; trivial
      revert hmem
      refine AddSubgroup.closure_induction
        (p := fun w _ => ∃ z, μ (cls p) w + μ w (cls p) = 2 • z) ?_ ?_ ?_ ?_
      · intro w hw
        obtain ⟨q, rfl⟩ := hw
        exact hgen p q
      · exact ⟨0, by simp⟩
      · intro a b _ _ ⟨za, ha⟩ ⟨zb, hb⟩
        refine ⟨za + zb, ?_⟩
        rw [show μ (cls p) (a + b) + μ (a + b) (cls p)
              = (μ (cls p) a + μ a (cls p)) + (μ (cls p) b + μ b (cls p)) from by
            simp only [map_add, AddMonoidHom.add_apply]
            abel,
          ha, hb, smul_add]
      · intro a _ ⟨za, ha⟩
        refine ⟨-za, ?_⟩
        rw [show μ (cls p) (-a) + μ (-a) (cls p) = -(μ (cls p) a + μ a (cls p)) from by
            simp only [map_neg, AddMonoidHom.neg_apply]
            abel,
          ha, smul_neg]
    intro x y
    have hmem : x ∈ AddSubgroup.closure (Set.range (cls : Mat A → K0 A)) := by
      rw [cls_closure_top]; trivial
    revert hmem
    refine AddSubgroup.closure_induction
      (p := fun w _ => ∃ z, μ w y + μ y w = 2 • z) ?_ ?_ ?_ ?_
    · intro w hw
      obtain ⟨p, rfl⟩ := hw
      exact hstep p y
    · exact ⟨0, by simp⟩
    · intro a b _ _ ⟨za, ha⟩ ⟨zb, hb⟩
      refine ⟨za + zb, ?_⟩
      rw [show μ (a + b) y + μ y (a + b)
            = (μ a y + μ y a) + (μ b y + μ y b) from by
          simp only [map_add, AddMonoidHom.add_apply]
          abel,
        ha, hb, smul_add]
    · intro a _ ⟨za, ha⟩
      refine ⟨-za, ?_⟩
      rw [show μ (-a) y + μ y (-a) = -(μ a y + μ y a) from by
          simp only [map_neg, AddMonoidHom.neg_apply]
          abel,
        ha, smul_neg]
  have hgen : ∀ p : Mat A, ∃ y, ψ2 (cls p) - μ (cls p) (cls p) = 2 • y := by
    intro p
    by_cases hp : p.IsIdem
    · refine ⟨-cls (sq2Part (-1) p), ?_⟩
      rw [h2 p,
        show μ (cls p) (cls p) = cls (p.kron p) from by
          rw [hμ]; unfold mulCls; rw [if_pos ⟨hp, hp⟩],
        show psi2Cls p = cls (sq2Part 1 p) - cls (sq2Part (-1) p) from by
          unfold psi2Cls; rw [if_pos hp],
        Psi.sq2Part_split hA hp]
      abel
    · refine ⟨0, ?_⟩
      rw [h2 p, show psi2Cls p = 0 from by unfold psi2Cls; rw [if_neg hp],
        show μ (cls p) (cls p) = 0 from by
          rw [hμ]; unfold mulCls; rw [if_neg (fun h => hp h.1)]]
      simp
  intro x
  have htop : (AddSubgroup.closure (Set.range (cls : Mat A → K0 A))) ≤
      { carrier := {x | ∃ y, ψ2 x - μ x x = 2 • y}
        zero_mem' := ⟨0, by simp⟩
        add_mem' := by
          rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
          obtain ⟨z, hz⟩ := hcross a b
          refine ⟨ya + yb - z, ?_⟩
          rw [show ψ2 (a + b) - μ (a + b) (a + b)
                = (ψ2 a - μ a a) + (ψ2 b - μ b b) - (μ a b + μ b a) from by
              simp only [map_add, AddMonoidHom.add_apply]
              abel,
            ha, hb, hz, smul_sub, smul_add]
        neg_mem' := by
          rintro a ⟨ya, ha⟩
          refine ⟨-(ya + μ a a), ?_⟩
          rw [show ψ2 (-a) - μ (-a) (-a) = -(ψ2 a - μ a a) - 2 • μ a a from by
              simp only [map_neg, AddMonoidHom.neg_apply]
              abel,
            ha]
          rw [smul_neg]
          abel } := by
    rw [AddSubgroup.closure_le]
    rintro x ⟨p, rfl⟩
    exact hgen p
  have hmem : x ∈ AddSubgroup.closure (Set.range (cls : Mat A → K0 A)) := by
    rw [cls_closure_top]; trivial
  exact htop hmem

end

/-- The Adams operations `ψ²`, `ψ³` exist on `K₀` of every commutative `ℂ`-algebra, are natural
for algebra maps, are multiplicative, and `ψ²(x) ≡ x² (mod 2)`. -/
theorem psi_exists :
    (∀ (A : Type) [Ring A] [Algebra ℂ A], (∀ x y : A, x * y = y * x) →
      (∃ ψ : K0 A →+ K0 A, IsPsi2 ψ) ∧ ∃ ψ : K0 A →+ K0 A, IsPsi3 ψ) ∧
    (∀ (A B : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B],
      (∀ x y : A, x * y = y * x) → (∀ x y : B, x * y = y * x) → ∀ (φ : A →ₐ[ℂ] B)
      (ψA : K0 A →+ K0 A) (ψB : K0 B →+ K0 B),
      (IsPsi2 ψA → IsPsi2 ψB → ∀ x, K0.mapA φ (ψA x) = ψB (K0.mapA φ x)) ∧
      (IsPsi3 ψA → IsPsi3 ψB → ∀ x, K0.mapA φ (ψA x) = ψB (K0.mapA φ x))) ∧
    (∀ (A : Type) [Ring A] [Algebra ℂ A], (∀ x y : A, x * y = y * x) →
      ∀ (μ : K0 A →+ K0 A →+ K0 A) (ψ2 ψ3 : K0 A →+ K0 A), IsK0Mul μ → IsPsi2 ψ2 → IsPsi3 ψ3 →
        ∀ x y, ψ2 (μ x y) = μ (ψ2 x) (ψ2 y) ∧ ψ3 (μ x y) = μ (ψ3 x) (ψ3 y)) ∧
    ∀ (A : Type) [Ring A] [Algebra ℂ A], (∀ x y : A, x * y = y * x) →
      ∀ (μ : K0 A →+ K0 A →+ K0 A) (ψ2 : K0 A →+ K0 A), IsK0Mul μ → IsPsi2 ψ2 →
        ∀ x, ∃ y, ψ2 x - μ x x = 2 • y := by
  refine ⟨fun A _ _ hA => ⟨psi2_exists hA, psi3_exists hA⟩,
    fun A B _ _ _ _ hA hB φ ψA ψB => ⟨fun h2 h2' => psi2_nat φ hA ψA ψB h2 h2',
      fun h3 h3' => psi3_nat φ hA ψA ψB h3 h3'⟩,
    fun A _ _ hA μ ψ2 ψ3 hμ h2 h3 x y =>
      ⟨psi2_mul hA μ ψ2 hμ h2 x y, psi3_mul hA μ ψ3 hμ h3 x y⟩,
    fun A _ _ hA μ ψ2 hμ h2 => psi2_mod_two hA μ ψ2 hμ h2⟩

end Work.KT
