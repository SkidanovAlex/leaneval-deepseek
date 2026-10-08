import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.ChV3.Prove.A_LV_aux
import Submission.Work.ThmF.ChV3.Prove.L_facts
import Submission.Work.ThmF.ChV3.Prove.W_V_on_L

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.A_LV_facts` — Peterfalvi II Ch. V §3, step (15d)

The leaf `15d` of the §3 design: with `A = Z₁ P Σ`, `L = X₅ ∩ C_G(st)`, `V = C_D(t)` and
`W = C_V(K)`,

* `A` is elementary abelian of order `27`;
* `Z₁ ⊓ (P ⊔ Σ) = ⊥`;
* `|L V| = 27 |W|`, `A ≤ L V`, and `Ω₁(L V) = A`;
* `Z₁ Σ` is central in `L V`.

All the structural input lives in `Prove/A_LV_aux`; here we assemble the seven conjuncts.
The two computations are `L_conj3` (`l (blb⁻¹) (b²lb⁻²) = l³`, using `[L,P] ≤ Z₁`) and its `W`
analogue, which turn `(l w b)³` into `l³ w³`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

open scoped Pointwise

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}

/-! ## Generic helpers -/

/-- `C_G(X) ⊓ C_G(Y) ≤ C_G(X ⊔ Y)`. -/
theorem centralizer_inf_le_centralizer_sup {G : Type} [Group G] {X Y : Subgroup G} :
    Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (Y : Set G) ≤
      Subgroup.centralizer ((X ⊔ Y : Subgroup G) : Set G) := by
  intro z hz
  obtain ⟨hzX, hzY⟩ := Subgroup.mem_inf.mp hz
  rw [Subgroup.mem_centralizer_iff] at hzX hzY ⊢
  intro w hw
  have h1 : X ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hzX x hx
  have h2 : Y ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hzY x hx
  have h3 := (sup_le h1 h2) hw
  rwa [Subgroup.mem_centralizer_singleton_iff] at h3

/-- The centraliser relation is symmetric between its two arguments. -/
theorem le_centralizer_comm {G : Type} [Group G] {A B : Subgroup G}
    (h : A ≤ Subgroup.centralizer (B : Set G)) : B ≤ Subgroup.centralizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact ((Subgroup.mem_centralizer_iff.mp (h ha)) b hb).symm

/-- A centralising subgroup normalises. -/
theorem centralizer_le_normalizer {G : Type} [Group G] (A : Subgroup G) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  intro x hx
  rw [← cj_eq_self_iff x A]
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    show (MulAut.conj x) z ∈ A
    have hc : z * x = x * z := (Subgroup.mem_centralizer_iff.mp hx) z hz
    rwa [show (MulAut.conj x) z = z by rw [MulAut.conj_apply, hc.symm]; group]
  · intro y hy
    refine ⟨y, hy, ?_⟩
    show (MulAut.conj x) y = y
    have hc : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hx) y hy
    rw [MulAut.conj_apply, ← hc]
    group

/-- Middle swap: `(x y)(u v) = (x u)(y v)` when `y u = u y`. -/
theorem swap_mul {G : Type} [Group G] {x y u v : G} (h : y * u = u * y) :
    (x * y) * (u * v) = (x * u) * (y * v) := by
  rw [mul_assoc x y (u * v), ← mul_assoc y u v, h, mul_assoc u y v, ← mul_assoc x u (y * v)]

/-- `l (l ζ) ((l ζ) ζ) = l³ ζ³` when `ζ l = l ζ`. -/
theorem rearrange_comm {G : Type} [Group G] {l ζ : G} (h : ζ * l = l * ζ) :
    l * (l * ζ) * ((l * ζ) * ζ) = l ^ 3 * ζ ^ 3 := by
  have hswap : ∀ A B : G, (A * ζ) * (l * B) = (A * l) * (ζ * B) := by
    intro A B
    rw [← mul_assoc (A * ζ) l B, mul_assoc A ζ l, h, ← mul_assoc A l ζ, mul_assoc (A * l) ζ B]
  have key : l * (l * ζ) * ((l * ζ) * ζ) = ((l * l) * l) * ((ζ * ζ) * ζ) := by
    calc l * (l * ζ) * ((l * ζ) * ζ) = ((l * l) * ζ) * (l * (ζ * ζ)) := by
          rw [← mul_assoc l l ζ, mul_assoc l ζ ζ]
      _ = ((l * l) * l) * (ζ * (ζ * ζ)) := hswap (l * l) (ζ * ζ)
      _ = ((l * l) * l) * ((ζ * ζ) * ζ) := by rw [mul_assoc ζ ζ ζ]
  rw [key]
  rw [show l ^ 3 = l * l * l from by rw [pow_succ, pow_two],
    show ζ ^ 3 = ζ * ζ * ζ from by rw [pow_succ, pow_two]]

/-- `(l w)(l₁ w₁)(l₂ w₂) = (l l₁ l₂)(w w₁ w₂)` when the two families commute across. -/
theorem rearrange_six {G : Type} [Group G] {l l1 l2 w w1 w2 : G}
    (h1 : w * l1 = l1 * w) (h2 : w1 * l2 = l2 * w1) (h3 : w * l2 = l2 * w) :
    (l * w) * (l1 * w1) * (l2 * w2) = (l * l1 * l2) * (w * w1 * w2) := by
  rw [swap_mul h1, mul_assoc (l * l1) (w * w1) (l2 * w2), swap_mul h2, h3,
    show (l * l1) * ((l2 * w) * (w1 * w2)) = ((l * l1) * l2) * (w * (w1 * w2)) from by group,
    ← mul_assoc w w1 w2]

/-! ## Commutation inside `L`, `W`, `P`, `Σ` -/

/-- `L` is abelian. -/
theorem comm_Lsub (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    ∀ x ∈ Lsub H s t, ∀ y ∈ Lsub H s t, x * y = y * x := by
  obtain ⟨g, -, hgen⟩ := exists_gen_zpowers_of_isCyclic (Lsub_isCyclic hFT hC4 c h15 d)
  intro x hx y hy
  exact commute_of_mem_zpowers (hgen.symm ▸ hx) (hgen.symm ▸ hy)

/-- `W` is abelian. -/
theorem comm_W (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    ∀ x ∈ W H t, ∀ y ∈ W H t, x * y = y * x := by
  obtain ⟨g, -, hgen⟩ := exists_gen_zpowers_of_isCyclic d.Wcyc
  intro x hx y hy
  exact commute_of_mem_zpowers (hgen.symm ▸ hx) (hgen.symm ▸ hy)

/-- `P` is abelian (it has order `3`). -/
theorem comm_P (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    P ≤ Subgroup.centralizer (P : Set G) := by
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  rcases eq_or_ne p 1 with rfl | hp1
  · rw [one_mul, mul_one]
  · have hpeq : Subgroup.zpowers p = P := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hp) ?_
      have hd : orderOf p ∣ 3 := by
        rw [← P_card d]; exact Subgroup.orderOf_dvd_natCard P hp
      have hne : orderOf p ≠ 1 := fun h => hp1 (orderOf_eq_one_iff.mp h)
      have h3 : orderOf p = 3 := by
        rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (orderOf p) hd with h | h
        · exact absurd h hne
        · exact h
      rw [Nat.card_zpowers, h3, P_card d]
    have hq' : q ∈ Subgroup.zpowers p := by rw [hpeq]; exact hq
    exact commute_of_mem_zpowers hq' (Subgroup.zpowers_le.mp le_rfl)

/-- `Σ` is abelian. -/
theorem comm_Sig (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    Sig H t P ≤ Subgroup.centralizer (Sig H t P : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact comm_W d y (Sig_le_W hy) x (Sig_le_W hx)

/-! ## The two conjugation computations -/

/-- `l (b l b⁻¹) (b² l b⁻²) = l³` for `l ∈ L`, `b ∈ P` (uses `[L,P] ≤ Z₁`). -/
theorem L_conj3 (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    ∀ l ∈ Lsub H s t, ∀ b ∈ P,
      l * (b * l * b⁻¹) * (b ^ 2 * l * (b ^ 2)⁻¹) = l ^ 3 := by
  intro l hl b hb
  have hζ : b * l * b⁻¹ * l⁻¹ ∈ Z1 s t := commutator_L_P hFT hC4 c h15 d l hl b hb
  set ζ := b * l * b⁻¹ * l⁻¹ with hζdef
  have hZl : ζ ∈ Lsub H s t := Z1_le_Lsub c hζ
  have h1 : b * l * b⁻¹ = ζ * l := by rw [hζdef]; group
  have hbζ : b * ζ * b⁻¹ = ζ := by
    have hc : b * ζ = ζ * b :=
      (Subgroup.mem_centralizer_iff.mp (Z1_le_centralizer_P c hζ)) b hb
    rw [show b * ζ * b⁻¹ = ζ by rw [hc]; group]
  have h2 : b ^ 2 * l * (b ^ 2)⁻¹ = (ζ * ζ) * l := by
    rw [show b ^ 2 = b * b from pow_two b, show (b * b)⁻¹ = b⁻¹ * b⁻¹ from mul_inv_rev b b]
    calc (b * b) * l * (b⁻¹ * b⁻¹) = b * (b * l * b⁻¹) * b⁻¹ := by group
      _ = b * (ζ * l) * b⁻¹ := by rw [h1]
      _ = (b * ζ * b⁻¹) * (b * l * b⁻¹) := by group
      _ = ζ * (ζ * l) := by rw [hbζ, h1]
      _ = (ζ * ζ) * l := by group
  have hζ3 : ζ ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by
    rw [← Z1_card d]; exact Subgroup.orderOf_dvd_natCard (Z1 s t) hζ)
  have hζl : ζ * l = l * ζ := comm_Lsub hFT hC4 c h15 d ζ hZl l hl
  rw [h1, h2, hζl, show (ζ * ζ) * l = (l * ζ) * ζ by rw [mul_assoc, hζl, ← mul_assoc, hζl],
    rearrange_comm hζl, hζ3, mul_one]

/-- `w (b w b⁻¹) (b² w b⁻²) = w³` for `w ∈ W`, `b ∈ P` (uses `[W,P] ≤ Σ`). -/
theorem W_conj3 (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    ∀ w ∈ W H t, ∀ b ∈ P,
      w * (b * w * b⁻¹) * (b ^ 2 * w * (b ^ 2)⁻¹) = w ^ 3 := by
  intro w hw b hb
  have hζ : b * w * b⁻¹ * w⁻¹ ∈ Sig H t P := commutator_W_P hFT hC4 c h15 d w hw b hb
  set ζ := b * w * b⁻¹ * w⁻¹ with hζdef
  have hZW : ζ ∈ W H t := Sig_le_W hζ
  have h1 : b * w * b⁻¹ = ζ * w := by rw [hζdef]; group
  have hbζ : b * ζ * b⁻¹ = ζ := by
    have hc : b * ζ = ζ * b :=
      (Subgroup.mem_centralizer_iff.mp (Sig_le_centralizer_P hζ)) b hb
    rw [show b * ζ * b⁻¹ = ζ by rw [hc]; group]
  have h2 : b ^ 2 * w * (b ^ 2)⁻¹ = (ζ * ζ) * w := by
    rw [show b ^ 2 = b * b from pow_two b, show (b * b)⁻¹ = b⁻¹ * b⁻¹ from mul_inv_rev b b]
    calc (b * b) * w * (b⁻¹ * b⁻¹) = b * (b * w * b⁻¹) * b⁻¹ := by group
      _ = b * (ζ * w) * b⁻¹ := by rw [h1]
      _ = (b * ζ * b⁻¹) * (b * w * b⁻¹) := by group
      _ = ζ * (ζ * w) := by rw [hbζ, h1]
      _ = (ζ * ζ) * w := by group
  have hζ3 : ζ ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by
    rw [← Sig_card d]; exact Subgroup.orderOf_dvd_natCard (Sig H t P) hζ)
  have hζl : ζ * w = w * ζ := comm_W d ζ hZW w hw
  rw [h1, h2, hζl, show (ζ * ζ) * w = (w * ζ) * ζ by rw [mul_assoc, hζl, ← mul_assoc, hζl],
    rearrange_comm hζl, hζ3, mul_one]

/-! ## The seven conjuncts -/

/-- `L V = (L ⊔ W) ⊔ P`. -/
theorem Lsub_sup_centD_eq (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P) :
    Lsub H s t ⊔ centD H t = (Lsub H s t ⊔ W H t) ⊔ P := by
  rw [← h15.hV]
  ac_rfl

/-- `A = Z₁ P Σ` is commutative. -/
theorem Asub_comm (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    IsMulCommutative ↥(Asub H P s t) := by
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  have hZ1 : Z1 s t ≤ Subgroup.centralizer (Asub H P s t : Set G) := by
    have h1 : Z1 s t ≤ Subgroup.centralizer (Z1 s t : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (comm_Lsub hFT hC4 c h15 d z (Z1_le_Lsub c hz) y (Z1_le_Lsub c hy)).symm
    have h2 : Z1 s t ≤ Subgroup.centralizer (P : Set G) := Z1_le_centralizer_P c
    have h3 : Z1 s t ≤ Subgroup.centralizer (Sig H t P : Set G) :=
      (Z1_le_centralizer_W hC4 c).trans (Subgroup.centralizer_le Sig_le_W)
    have h4 : Z1 s t ≤ Subgroup.centralizer (((Z1 s t ⊔ P) : Subgroup G) : Set G) :=
      (le_inf h1 h2).trans (centralizer_inf_le_centralizer_sup (X := Z1 s t) (Y := P))
    have h5 : Z1 s t ≤
        Subgroup.centralizer (((Z1 s t ⊔ P ⊔ Sig H t P) : Subgroup G) : Set G) :=
      (le_inf h4 h3).trans
        (centralizer_inf_le_centralizer_sup (X := Z1 s t ⊔ P) (Y := Sig H t P))
    exact h5
  have hP : P ≤ Subgroup.centralizer (Asub H P s t : Set G) := by
    have h1 : P ≤ Subgroup.centralizer (Z1 s t : Set G) :=
      le_centralizer_comm (Z1_le_centralizer_P c)
    have h2 : P ≤ Subgroup.centralizer (P : Set G) := comm_P d
    have h3 : P ≤ Subgroup.centralizer (Sig H t P : Set G) :=
      le_centralizer_comm Sig_le_centralizer_P
    have h4 : P ≤ Subgroup.centralizer (((Z1 s t ⊔ P) : Subgroup G) : Set G) :=
      (le_inf h1 h2).trans (centralizer_inf_le_centralizer_sup (X := Z1 s t) (Y := P))
    have h5 : P ≤ Subgroup.centralizer (((Z1 s t ⊔ P ⊔ Sig H t P) : Subgroup G) : Set G) :=
      (le_inf h4 h3).trans
        (centralizer_inf_le_centralizer_sup (X := Z1 s t ⊔ P) (Y := Sig H t P))
    exact h5
  have hS : Sig H t P ≤ Subgroup.centralizer (Asub H P s t : Set G) := by
    have h3 : Sig H t P ≤ Subgroup.centralizer (Z1 s t : Set G) :=
      le_centralizer_comm ((Z1_le_centralizer_W hC4 c).trans (Subgroup.centralizer_le Sig_le_W))
    have h4 : Sig H t P ≤ Subgroup.centralizer (((Z1 s t ⊔ P) : Subgroup G) : Set G) :=
      (le_inf h3 Sig_le_centralizer_P).trans
        (centralizer_inf_le_centralizer_sup (X := Z1 s t) (Y := P))
    have h5 : Sig H t P ≤
        Subgroup.centralizer (((Z1 s t ⊔ P ⊔ Sig H t P) : Subgroup G) : Set G) :=
      (le_inf h4 (comm_Sig d)).trans
        (centralizer_inf_le_centralizer_sup (X := Z1 s t ⊔ P) (Y := Sig H t P))
    exact h5
  exact sup_le (sup_le hZ1 hP) hS

/-- `|A| = 27`. -/
theorem Asub_card (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) : Nat.card ↥(Asub H P s t) = 27 := by
  have hN1 : P ≤ Subgroup.normalizer (Z1 s t : Set G) :=
    (le_centralizer_comm (Z1_le_centralizer_P c)).trans (centralizer_le_normalizer (Z1 s t))
  have hcard1 : Nat.card ↥(Z1 s t ⊔ P) = 9 := by
    rw [card_sup_of_le_normalizer hN1 (Z1_inf_P_eq_bot hFT hC4 c h15 d), Z1_card d, P_card d]
  have hSigC : Sig H t P ≤ Subgroup.centralizer (((Z1 s t ⊔ P) : Subgroup G) : Set G) :=
    (le_inf (le_centralizer_comm
      ((Z1_le_centralizer_W hC4 c).trans (Subgroup.centralizer_le Sig_le_W)))
      Sig_le_centralizer_P).trans
      (centralizer_inf_le_centralizer_sup (X := Z1 s t) (Y := P))
  have hN2 : Sig H t P ≤
      Subgroup.normalizer (((Z1 s t ⊔ P) : Subgroup G) : Set G) :=
    hSigC.trans (centralizer_le_normalizer ((Z1 s t ⊔ P : Subgroup G)))
  have hinf2 : (Z1 s t ⊔ P) ⊓ Sig H t P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨hgZP, hgS⟩ := Subgroup.mem_inf.mp hg
    have hgV : g ∈ centD H t := (Sig_le_W.trans (W_le_centD H t)) hgS
    have hcoe : (↑(Z1 s t ⊔ P) : Set G) = (Z1 s t : Set G) * (P : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN1
    have hg' : g ∈ (Z1 s t : Set G) * (P : Set G) := by rw [← hcoe]; exact hgZP
    obtain ⟨z, hz, p, hp, hzp⟩ := Set.mem_mul.mp hg'
    have hzV : z ∈ centD H t := by
      have hz' : z = g * p⁻¹ := by rw [← hzp]; group
      rw [hz']
      exact (centD H t).mul_mem hgV ((centD H t).inv_mem (c.P_le hp))
    have hz1 : z = 1 := by
      have hmem : z ∈ Lsub H s t ⊓ centD H t := ⟨Z1_le_Lsub c hz, hzV⟩
      rw [Lsub_inf_centD_eq_bot hFT hC4 c h15 d] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hgp : g = p := by rw [← hzp, hz1, one_mul]
    have hmem : g ∈ P ⊓ Sig H t P := ⟨hgp ▸ hp, hgS⟩
    rw [P_inf_Sig_eq_bot h15] at hmem
    exact Subgroup.mem_bot.mp hmem
  rw [card_sup_of_le_normalizer hN2 hinf2, hcard1, Sig_card d]

/-- `L ⊔ V` has order `27 |W|`. -/
theorem card_LV (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    Nat.card ↥(Lsub H s t ⊔ centD H t) = 27 * Nat.card ↥(W H t) := by
  rw [Lsub_sup_centD_eq h15]
  have h1 : Nat.card ↥(Lsub H s t ⊔ W H t) = 9 * Nat.card ↥(W H t) := by
    rw [card_sup_of_le_normalizer (W_le_normalizer_Lsub hC4 c)
      (Lsub_inf_W_eq_bot hFT hC4 c h15 d), Lsub_card hFT hC4 c h15 d]
  rw [card_sup_of_le_normalizer (P_le_normalizer_Lsub_sup_W (H := H) (t := t) c)
    (Lsub_sup_W_inf_P_eq_bot hFT hC4 c h15 d), h1, P_card d]
  ring

/-- `A ≤ L ⊔ V`. -/
theorem Asub_le_LV (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P) :
    Asub H P s t ≤ Lsub H s t ⊔ centD H t := by
  rw [Asub, ← h15.hV]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_sup_of_le_left (Z1_le_Lsub c)
  · exact le_sup_of_le_right le_sup_right
  · exact le_sup_of_le_right (Sig_le_W.trans le_sup_left)

/-- `Ω₁(L V) ⊆ A`. -/
theorem omega1_LV_le_Asub (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    ∀ x ∈ Lsub H s t ⊔ centD H t, x ^ 3 = 1 → x ∈ Asub H P s t := by
  intro x hx hx3
  rw [Lsub_sup_centD_eq h15] at hx
  -- decompose `x = a * b` with `a ∈ L ⊔ W`, `b ∈ P`
  have hcoe : (↑((Lsub H s t ⊔ W H t) ⊔ P) : Set G) =
      (((Lsub H s t ⊔ W H t : Subgroup G)) : Set G) * (P : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (P_le_normalizer_Lsub_sup_W (H := H) (t := t) c)
  have hx' : x ∈ (((Lsub H s t ⊔ W H t : Subgroup G)) : Set G) * (P : Set G) := by
    rw [← hcoe]; exact hx
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx'
  -- decompose `a = l * w`
  have hcoe2 : (↑(Lsub H s t ⊔ W H t) : Set G) =
      (Lsub H s t : Set G) * (W H t : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (W_le_normalizer_Lsub hC4 c)
  have ha' : a ∈ (Lsub H s t : Set G) * (W H t : Set G) := by rw [← hcoe2]; exact ha
  obtain ⟨l, hl, w, hw, hlw⟩ := Set.mem_mul.mp ha'
  have hb3 : b ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by
    rw [← P_card d]; exact Subgroup.orderOf_dvd_natCard P hb)
  -- the conjugated pieces stay in `L` and `W`
  have hbl : b * l * b⁻¹ ∈ Lsub H s t :=
    (Subgroup.mem_normalizer_iff.mp (P_le_normalizer_Lsub c hb) l).mp hl
  have hbw : b * w * b⁻¹ ∈ W H t :=
    (Subgroup.mem_normalizer_iff.mp (P_le_normalizer_W c hb) w).mp hw
  have hb2N : b ^ 2 ∈ Subgroup.normalizer (Lsub H s t : Set G) := by
    rw [show b ^ 2 = b * b from pow_two b]
    exact (Subgroup.normalizer (Lsub H s t : Set G)).mul_mem
      (P_le_normalizer_Lsub c hb) (P_le_normalizer_Lsub c hb)
  have hb2l : b ^ 2 * l * (b ^ 2)⁻¹ ∈ Lsub H s t :=
    (Subgroup.mem_normalizer_iff.mp hb2N l).mp hl
  have hb2NW : b ^ 2 ∈ Subgroup.normalizer (W H t : Set G) := by
    rw [show b ^ 2 = b * b from pow_two b]
    exact (Subgroup.normalizer (W H t : Set G)).mul_mem
      (P_le_normalizer_W c hb) (P_le_normalizer_W c hb)
  have hb2w : b ^ 2 * w * (b ^ 2)⁻¹ ∈ W H t :=
    (Subgroup.mem_normalizer_iff.mp hb2NW w).mp hw
  -- `x³ = l³ w³`
  have hconj1 : b * a * b⁻¹ = (b * l * b⁻¹) * (b * w * b⁻¹) := by
    rw [← hlw]; group
  have hconj2 : b ^ 2 * a * (b ^ 2)⁻¹ =
      (b ^ 2 * l * (b ^ 2)⁻¹) * (b ^ 2 * w * (b ^ 2)⁻¹) := by
    rw [← hlw]; group
  have hx3form : x ^ 3 = a * (b * a * b⁻¹) * (b ^ 2 * a * (b ^ 2)⁻¹) := by
    rw [← hab]
    have h1 : (a * b) ^ 3 = (a * b) * (a * b) * (a * b) := by rw [pow_succ, pow_two]
    have h2 : (a * b) * (a * b) * (a * b) =
        a * (b * a * b⁻¹) * (b ^ 2 * a * (b ^ 2)⁻¹) * b ^ 3 := by
      rw [show b ^ 2 = b * b from pow_two b, show (b * b)⁻¹ = b⁻¹ * b⁻¹ from mul_inv_rev b b]
      group
    rw [h1, h2, hb3, mul_one]
  have hcomm1 : w * (b * l * b⁻¹) = (b * l * b⁻¹) * w :=
    (comm_Lsub_W hC4 c (b * l * b⁻¹) hbl w hw).symm
  have hcomm2 : (b * w * b⁻¹) * (b ^ 2 * l * (b ^ 2)⁻¹) =
      (b ^ 2 * l * (b ^ 2)⁻¹) * (b * w * b⁻¹) :=
    (comm_Lsub_W hC4 c (b ^ 2 * l * (b ^ 2)⁻¹) hb2l (b * w * b⁻¹) hbw).symm
  have hcomm3 : w * (b ^ 2 * l * (b ^ 2)⁻¹) = (b ^ 2 * l * (b ^ 2)⁻¹) * w :=
    (comm_Lsub_W hC4 c (b ^ 2 * l * (b ^ 2)⁻¹) hb2l w hw).symm
  have hkey : x ^ 3 = l ^ 3 * w ^ 3 := by
    rw [hx3form, hconj1, hconj2]
    rw [show a = l * w from hlw.symm]
    rw [rearrange_six (l := l) (l1 := b * l * b⁻¹) (l2 := b ^ 2 * l * (b ^ 2)⁻¹)
        (w := w) (w1 := b * w * b⁻¹) (w2 := b ^ 2 * w * (b ^ 2)⁻¹) hcomm1 hcomm2 hcomm3]
    rw [L_conj3 hFT hC4 c h15 d l hl b hb, W_conj3 hFT hC4 c h15 d w hw b hb]
  -- conclusion
  have hmul : l ^ 3 * w ^ 3 = 1 := by rw [← hkey]; exact hx3
  have hl3Z : l ^ 3 ∈ Z1 s t := Lsub_pow3_mem_Z1 hFT hC4 c h15 d l hl
  have hl3S : l ^ 3 ∈ Sig H t P := by
    have h2 : l ^ 3 = (w ^ 3)⁻¹ := by
      calc l ^ 3 = l ^ 3 * (w ^ 3 * (w ^ 3)⁻¹) := by group
        _ = (l ^ 3 * w ^ 3) * (w ^ 3)⁻¹ := by group
        _ = 1 * (w ^ 3)⁻¹ := by rw [hmul]
        _ = (w ^ 3)⁻¹ := by rw [one_mul]
    rw [h2]
    exact (Sig H t P).inv_mem (W_pow3_mem_Sig hFT hC4 c h15 d w hw)
  have hl3 : l ^ 3 = 1 := by
    have hmem : l ^ 3 ∈ Z1 s t ⊓ Sig H t P := ⟨hl3Z, hl3S⟩
    rw [Z1_inf_Sig_eq_bot hFT hC4 c h15 d] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hw3 : w ^ 3 = 1 := by
    rw [hl3, one_mul] at hmul
    exact hmul
  have hlZ : l ∈ Z1 s t := (Lsub_pow3_eq_one_iff hFT hC4 c h15 d l hl).mp hl3
  have hwS : w ∈ Sig H t P := (W_pow3_eq_one_iff hFT hC4 c h15 d w hw).mp hw3
  have hxeq : x = l * w * b := by rw [← hab, ← hlw]
  rw [hxeq, Asub]
  have hmem : l * (w * b) ∈ Z1 s t ⊔ (Sig H t P ⊔ P) :=
    Subgroup.mul_mem_sup hlZ (Subgroup.mul_mem_sup hwS hb)
  rw [show l * (w * b) = l * w * b from (mul_assoc l w b).symm] at hmem
  rwa [show (Z1 s t ⊔ (Sig H t P ⊔ P) : Subgroup G) = Z1 s t ⊔ P ⊔ Sig H t P from by
    ac_rfl] at hmem

/-- `Z₁ Σ` is central in `L V`. -/
theorem Z1_sup_Sig_central (hFT : FeitThompsonProp) (hC4 : ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    ∀ a ∈ Z1 s t ⊔ Sig H t P, ∀ y ∈ Lsub H s t ⊔ centD H t, a * y = y * a := by
  have hC : Z1 s t ⊔ Sig H t P ≤
      Subgroup.centralizer (((Lsub H s t ⊔ W H t ⊔ P : Subgroup G)) : Set G) := by
    have hZ1' : Z1 s t ≤ Subgroup.centralizer (Lsub H s t : Set G) :=
      Z1_le_centralizer_Lsub hFT hC4 c h15 d
    have hZ2 : Z1 s t ≤ Subgroup.centralizer (W H t : Set G) := Z1_le_centralizer_W hC4 c
    have hZ3 : Z1 s t ≤ Subgroup.centralizer (P : Set G) := Z1_le_centralizer_P c
    have hZ4 : Z1 s t ≤ Subgroup.centralizer (((Lsub H s t ⊔ W H t) : Subgroup G) : Set G) :=
      (le_inf hZ1' hZ2).trans (centralizer_inf_le_centralizer_sup (X := Lsub H s t) (Y := W H t))
    have hZ5 : Z1 s t ≤
        Subgroup.centralizer (((Lsub H s t ⊔ W H t ⊔ P : Subgroup G)) : Set G) :=
      (le_inf hZ4 hZ3).trans
        (centralizer_inf_le_centralizer_sup (X := Lsub H s t ⊔ W H t) (Y := P))
    have hS1 : Sig H t P ≤ Subgroup.centralizer (Lsub H s t : Set G) :=
      Sig_le_centralizer_Lsub hC4 c
    have hS2 : Sig H t P ≤ Subgroup.centralizer (W H t : Set G) := Sig_le_centralizer_W d
    have hS3 : Sig H t P ≤ Subgroup.centralizer (P : Set G) := Sig_le_centralizer_P
    have hS4 : Sig H t P ≤ Subgroup.centralizer (((Lsub H s t ⊔ W H t) : Subgroup G) : Set G) :=
      (le_inf hS1 hS2).trans (centralizer_inf_le_centralizer_sup (X := Lsub H s t) (Y := W H t))
    have hS5 : Sig H t P ≤
        Subgroup.centralizer (((Lsub H s t ⊔ W H t ⊔ P : Subgroup G)) : Set G) :=
      (le_inf hS4 hS3).trans
        (centralizer_inf_le_centralizer_sup (X := Lsub H s t ⊔ W H t) (Y := P))
    exact sup_le hZ5 hS5
  intro a ha y hy
  rw [Lsub_sup_centD_eq h15] at hy
  exact ((Subgroup.mem_centralizer_iff.mp (hC ha)) y hy).symm

theorem A_LV_facts {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    IsMulCommutative ↥(Work.ThmF.ChV3.Asub H P s t) ∧
      Nat.card ↥(Work.ThmF.ChV3.Asub H P s t) = 27 ∧
      Work.ThmF.ChV3.Z1 s t ⊓ (P ⊔ Work.ThmF.ChV3.Sig H t P) = ⊥ ∧
      Nat.card ↥(Work.ThmF.ChV3.Lsub H s t ⊔ Submission.Blueprint.centD H t) =
        27 * Nat.card ↥(Work.ThmF.W H t) ∧
      Work.ThmF.ChV3.Asub H P s t ≤ Work.ThmF.ChV3.Lsub H s t ⊔
        Submission.Blueprint.centD H t ∧
      (∀ x ∈ Work.ThmF.ChV3.Lsub H s t ⊔ Submission.Blueprint.centD H t, x ^ 3 = 1 →
        x ∈ Work.ThmF.ChV3.Asub H P s t) ∧
      (∀ a ∈ Work.ThmF.ChV3.Z1 s t ⊔ Work.ThmF.ChV3.Sig H t P,
        ∀ y ∈ Work.ThmF.ChV3.Lsub H s t ⊔ Submission.Blueprint.centD H t,
        a * y = y * a) :=
  ⟨Asub_comm hFT hC4 c h15 d, Asub_card hFT hC4 c h15 d,
    Z1_inf_P_sup_Sig_eq_bot hFT hC4 c h15 d, card_LV hFT hC4 c h15 d,
    Asub_le_LV c h15, omega1_LV_le_Asub hFT hC4 c h15 d,
    Z1_sup_Sig_central hFT hC4 c h15 d⟩

end Work.ThmF.ChV3.Prove
