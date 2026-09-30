import Mathlib
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.adi_crt
import Submission.Work.BMF.polyrel_chain_ind
import Submission.Work.BMF.cycFac_basic
import Submission.Work.BMF.GAdjQ_iff_stepS_or

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.bike_adi_side`

The approximate-dilation-invariance relation carried around a closed walk of the quadruple
graph.  Given a closed walk `W` of length `ℓ` through the interval based at `x`, and a nonempty
set `S` of primes each of which lies in the prime set of every step of `W` (in one of the two
directions), the two ends of the walk -- i.e. the states `(1/∏V)_* φ_x` and `(1/∏U)_* φ_x` --
are `PolyRel`-comparable with modulus `1/∏S` and the iterated transitivity constant
`cycConst k (symmConst k (max C (symmConst k C))) ℓ`.

The proof composes, step by step, the edge relations `step_rel`; the Chinese remainder property
`polyRel_crt` upgrades each step to modulus `1/∏S`, the telescoping factors `cycFac`/`aaV` carry
the intermediate states through, and `polyrel_chain_ind` iterates the transitivity constant.
Whenever a step of the walk has to be traversed backwards, the two labels of the reversed edge
are swapped; that is the content of `step_labels_swap`.
-/

namespace Work.BMF

open Polynomial Finset Real

theorem step_labels_swap {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L)
    (hbig : 8000 * P₁ ^ 2 < X / L)
    {x y : GVert D} (hxy : stepFwd D x y) (hyx : stepFwd D y x) :
    stepV D x y = stepU D y x ∧ stepU D x y = stepV D y x := by
  classical
  obtain ⟨he, hex1, hex2⟩ := arcWit_spec D hxy
  obtain ⟨hf, hfx1, hfx2⟩ := arcWit_spec D hyx
  have hge := EdgeGeom.geom (D.geom (arcWit D x.1 y.1) he)
  rw [hex1, hex2] at hge
  have hgf := EdgeGeom.geom (D.geom (arcWit D y.1 x.1) hf)
  rw [hfx1, hfx2] at hgf
  set a : ℕ := (arcWit D x.1 y.1).p₁ with ha
  set b : ℕ := (arcWit D x.1 y.1).p₂ with hb
  set c : ℕ := (arcWit D y.1 x.1).p₁ with hc
  set d : ℕ := (arcWit D y.1 x.1).p₂ with hd
  have hpa : a.Prime := by rw [ha]; exact (EdgeGeom.prime_p₁ (D.geom (arcWit D x.1 y.1) he)).1
  have hpb : b.Prime := by rw [hb]; exact (EdgeGeom.prime_p₂ (D.geom (arcWit D x.1 y.1) he)).1
  have hpc : c.Prime := by rw [hc]; exact (EdgeGeom.prime_p₁ (D.geom (arcWit D y.1 x.1) hf)).1
  have hpd : d.Prime := by rw [hd]; exact (EdgeGeom.prime_p₂ (D.geom (arcWit D y.1 x.1) hf)).1
  have haP : (a:ℝ) ≤ 2 * P₁ := by rw [ha]; exact (EdgeGeom.prime_p₁ (D.geom (arcWit D x.1 y.1) he)).2.2
  have hbP : (b:ℝ) ≤ 2 * P₁ := by rw [hb]; exact (EdgeGeom.prime_p₂ (D.geom (arcWit D x.1 y.1) he)).2.2
  have hcP : (c:ℝ) ≤ 2 * P₁ := by rw [hc]; exact (EdgeGeom.prime_p₁ (D.geom (arcWit D y.1 x.1) hf)).2.2
  have hab_ne : a ≠ b := by rw [ha, hb]; exact EdgeGeom.p_ne (D.geom (arcWit D x.1 y.1) he)
  have haR : (0:ℝ) < a := by exact_mod_cast hpa.pos
  have hbR : (0:ℝ) < b := by exact_mod_cast hpb.pos
  have hcR : (0:ℝ) < c := by exact_mod_cast hpc.pos
  have hdR : (0:ℝ) < d := by exact_mod_cast hpd.pos
  have hL0 : (0:ℝ) ≤ L := hL.le
  have h1 : |(a:ℝ)*x.1 - (b:ℝ)*y.1| ≤ 100*L*(a:ℝ) := by
    have key : (a:ℝ)*x.1 - (b:ℝ)*y.1 = (a:ℝ)*(x.1 - ((b:ℝ)/(a:ℝ))*y.1) := by
      field_simp
    rw [key, abs_mul, abs_of_pos haR]
    calc (a:ℝ) * |x.1 - ((b:ℝ)/(a:ℝ))*y.1| ≤ (a:ℝ) * (100*L) :=
          mul_le_mul_of_nonneg_left hge haR.le
      _ = 100*L*(a:ℝ) := by ring
  have h1' : |(a:ℝ)*(c:ℝ)*x.1 - (b:ℝ)*(c:ℝ)*y.1| ≤ 100*L*(a:ℝ)*(c:ℝ) := by
    have key : (a:ℝ)*(c:ℝ)*x.1 - (b:ℝ)*(c:ℝ)*y.1
        = (c:ℝ)*((a:ℝ)*x.1 - (b:ℝ)*y.1) := by ring
    rw [key, abs_mul, abs_of_pos hcR]
    calc (c:ℝ) * |(a:ℝ)*x.1 - (b:ℝ)*y.1| ≤ (c:ℝ) * (100*L*(a:ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hcR.le
      _ = 100*L*(a:ℝ)*(c:ℝ) := by ring
  have h2 : |(c:ℝ)*y.1 - (d:ℝ)*x.1| ≤ 100*L*(c:ℝ) := by
    have key : (c:ℝ)*y.1 - (d:ℝ)*x.1 = (c:ℝ)*(y.1 - ((d:ℝ)/(c:ℝ))*x.1) := by
      field_simp
    rw [key, abs_mul, abs_of_pos hcR]
    calc (c:ℝ) * |y.1 - ((d:ℝ)/(c:ℝ))*x.1| ≤ (c:ℝ) * (100*L) :=
          mul_le_mul_of_nonneg_left hgf hcR.le
      _ = 100*L*(c:ℝ) := by ring
  have h2' : |(b:ℝ)*(c:ℝ)*y.1 - (b:ℝ)*(d:ℝ)*x.1| ≤ 100*L*(c:ℝ)*(b:ℝ) := by
    have key : (b:ℝ)*(c:ℝ)*y.1 - (b:ℝ)*(d:ℝ)*x.1
        = (b:ℝ)*((c:ℝ)*y.1 - (d:ℝ)*x.1) := by ring
    rw [key, abs_mul, abs_of_pos hbR]
    calc (b:ℝ) * |(c:ℝ)*y.1 - (d:ℝ)*x.1| ≤ (b:ℝ) * (100*L*(c:ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hbR.le
      _ = 100*L*(c:ℝ)*(b:ℝ) := by ring
  have htri : |((a:ℝ)*(c:ℝ) - (b:ℝ)*(d:ℝ)) * x.1|
      ≤ |(a:ℝ)*(c:ℝ)*x.1 - (b:ℝ)*(c:ℝ)*y.1| + |(b:ℝ)*(c:ℝ)*y.1 - (b:ℝ)*(d:ℝ)*x.1| := by
    rw [show ((a:ℝ)*(c:ℝ) - (b:ℝ)*(d:ℝ)) * x.1
        = ((a:ℝ)*(c:ℝ)*x.1 - (b:ℝ)*(c:ℝ)*y.1)
          + ((b:ℝ)*(c:ℝ)*y.1 - (b:ℝ)*(d:ℝ)*x.1) by ring]
    exact abs_add_le _ _
  have hsum : |((a:ℝ)*(c:ℝ) - (b:ℝ)*(d:ℝ)) * x.1| ≤ 100*L*(c:ℝ)*((a:ℝ)+(b:ℝ)) := by
    calc |((a:ℝ)*(c:ℝ) - (b:ℝ)*(d:ℝ)) * x.1|
        ≤ |(a:ℝ)*(c:ℝ)*x.1 - (b:ℝ)*(c:ℝ)*y.1| + |(b:ℝ)*(c:ℝ)*y.1 - (b:ℝ)*(d:ℝ)*x.1| := htri
      _ ≤ 100*L*(a:ℝ)*(c:ℝ) + 100*L*(c:ℝ)*(b:ℝ) := add_le_add h1' h2'
      _ = 100*L*(c:ℝ)*((a:ℝ)+(b:ℝ)) := by ring
  have hP0 : (0:ℝ) < P₁ := hP
  have hXpos : (0:ℝ) < X := by
    have h0 : (0:ℝ) < 8000 * P₁ ^ 2 := by positivity
    have h1 : (0:ℝ) < X / L := lt_of_lt_of_le h0 hbig.le
    exact (div_pos_iff_of_pos_right hL).mp h1
  have hx10 : X / 10 ≤ x.1 := (D.isFam.1 x.1 x.2).1
  have hx1pos : (0:ℝ) < x.1 := by linarith
  have hbnd : 100*L*(c:ℝ)*((a:ℝ)+(b:ℝ)) ≤ 800*L*P₁^2 := by
    have hc0 : (0:ℝ) ≤ (c:ℝ) := hcR.le
    have hab0 : (0:ℝ) ≤ (a:ℝ)+(b:ℝ) := by positivity
    have hab : (a:ℝ)+(b:ℝ) ≤ 4*P₁ := by linarith
    have hs1 : 100*L*(c:ℝ) ≤ 100*L*(2*P₁) :=
      mul_le_mul_of_nonneg_left hcP (by positivity)
    have hs2 : 100*L*(c:ℝ)*((a:ℝ)+(b:ℝ)) ≤ 100*L*(2*P₁)*((a:ℝ)+(b:ℝ)) :=
      mul_le_mul_of_nonneg_right hs1 hab0
    have hs3 : 100*L*(2*P₁)*((a:ℝ)+(b:ℝ)) ≤ 100*L*(2*P₁)*(4*P₁) :=
      mul_le_mul_of_nonneg_left hab (by positivity)
    have heq : 100*L*(2*P₁)*(4*P₁) = 800*L*P₁^2 := by ring
    linarith [hs2, hs3, heq.le, heq.ge]
  have hmain : |((a:ℝ)*(c:ℝ) - (b:ℝ)*(d:ℝ))| * (X/10) ≤ 800*L*P₁^2 := by
    have h1 : |((a:ℝ)*(c:ℝ) - (b:ℝ)*(d:ℝ))| * x.1 ≤ 800*L*P₁^2 := by
      rw [abs_mul, abs_of_pos hx1pos] at hsum
      linarith [hsum, hbnd]
    calc |((a:ℝ)*(c:ℝ) - (b:ℝ)*(d:ℝ))| * (X/10)
        ≤ |((a:ℝ)*(c:ℝ) - (b:ℝ)*(d:ℝ))| * x.1 :=
          mul_le_mul_of_nonneg_left hx10 (abs_nonneg _)
      _ ≤ 800*L*P₁^2 := h1
  have hlt : |(a:ℝ)*(c:ℝ) - (b:ℝ)*(d:ℝ)| < 1 := by
    have hX : |(a:ℝ)*(c:ℝ) - (b:ℝ)*(d:ℝ)| * X ≤ 8000*L*P₁^2 := by
      have := hmain
      linarith [this]
    have hbig' : 8000*L*P₁^2 < X := by
      have h := (lt_div_iff₀ hL).mp hbig
      linarith [h]
    nlinarith [hX, hbig', hXpos, abs_nonneg ((a:ℝ)*(c:ℝ) - (b:ℝ)*(d:ℝ))]
  have hnac : a * c = b * d := by
    by_contra hne
    have h1 : (1:ℝ) ≤ |((a*c:ℕ):ℝ) - ((b*d:ℕ):ℝ)| := one_le_abs_cast_sub_nat hne
    have h2 : |((a*c:ℕ):ℝ) - ((b*d:ℕ):ℝ)| < 1 := by
      push_cast
      linarith [hlt]
    linarith
  have hratio : (b:ℝ)/(a:ℝ) = (c:ℝ)/(d:ℝ) := by
    have hbd : (b:ℝ)*(d:ℝ) = (c:ℝ)*(a:ℝ) := by
      have h : (a:ℝ)*(c:ℝ) = (b:ℝ)*(d:ℝ) := by exact_mod_cast hnac
      linarith [h]
    rw [div_eq_div_iff (ne_of_gt haR) (ne_of_gt hdR)]
    linarith [hbd]
  obtain ⟨had, hbc⟩ := prime_ratio_inj hpa hpb hpd hab_ne hratio
  rw [stepV_fwd D hxy, stepU_fwd D hyx, stepU_fwd D hxy, stepV_fwd D hyx]
  rw [← hb, ← hc, ← ha, ← hd]
  exact ⟨hbc, had⟩

lemma GAdjAll_or_stepFwd {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : QuadData k f c C X L P₁ P₂) (x y : GVert D) :
    GAdjAll D x y ↔ stepFwd D x y ∨ stepFwd D y x := by
  constructor
  · rintro ⟨e, he, h | h⟩
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩
  · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩)
    · exact ⟨e, he, Or.inl h⟩
    · exact ⟨e, he, Or.inr h⟩

theorem polyRel_step_mem {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : QuadData k f c C X L P₁ P₂) (hC : 0 < C) (hP : 0 < P₁) (hL : 0 < L)
    (hbig : 8000 * P₁ ^ 2 < X / L)
    {x y : GVert D} (hxy : GAdjAll D x y) {p : ℕ}
    (hp : p ∈ stepS D x y ∨ p ∈ stepS D y x) :
    PolyRel k (symmConst k (max C (symmConst k C))) (1 / (p : ℝ))
      (x.1 / (stepV D x y : ℝ)) (L / (stepV D x y : ℝ)) (dil (stepV D x y : ℝ) (D.pol x.1))
      (y.1 / (stepU D x y : ℝ)) (L / (stepU D x y : ℝ)) (dil (stepU D x y : ℝ) (D.pol y.1)) := by
  classical
  have hC' : 0 < max C (symmConst k C) := lt_of_lt_of_le hC (le_max_left _ _)
  have hle : max C (symmConst k C) ≤ symmConst k (max C (symmConst k C)) :=
    symmConst_ge_self hC'
  have hxy' : stepFwd D x y ∨ stepFwd D y x := (GAdjAll_or_stepFwd D x y).mp hxy
  by_cases hp1 : p ∈ stepS D x y
  · have hadj : GAdjQ D p x y := GAdjQ_of_mem_stepS D hp1
    have hVp : 0 < (stepV D x y : ℝ) := by
      have := (stepV_prime D hadj).2.1; linarith [hP, this]
    have hUp : 0 < (stepU D x y : ℝ) := by
      have := (stepU_prime D hadj).2.1; linarith [hP, this]
    exact (step_rel D hC hL hP hadj hp1).mono hle (div_nonneg hL.le hVp.le)
      (div_nonneg hL.le hUp.le)
  · have hp2 : p ∈ stepS D y x := hp.resolve_left hp1
    have hfx : stepFwd D x y := by
      by_contra h
      have hfy : stepFwd D y x := hxy'.resolve_left h
      have h1 : stepWit D x y = arcWit D y.1 x.1 := stepWit_rev D h
      have h2 : stepWit D y x = arcWit D y.1 x.1 := stepWit_fwd D hfy
      have hseq : stepS D x y = stepS D y x := by rw [stepS_eq D x y, stepS_eq D y x, h1, h2]
      exact hp1 (hseq ▸ hp2)
    have hfy : stepFwd D y x := by
      by_contra h
      rcases hxy' with h' | h'
      · have h1 : stepWit D x y = arcWit D x.1 y.1 := stepWit_fwd D h'
        have h2 : stepWit D y x = arcWit D x.1 y.1 := stepWit_rev D h
        have hseq : stepS D x y = stepS D y x := by rw [stepS_eq D x y, stepS_eq D y x, h1, h2]
        exact hp1 (hseq ▸ hp2)
      · exact absurd h' h
    obtain ⟨hsw1, hsw2⟩ := step_labels_swap D hP hL hbig hfx hfy
    have hadj : GAdjQ D p y x := GAdjQ_of_mem_stepS D hp2
    have hVyp : 0 < (stepV D y x : ℝ) := by
      have := (stepV_prime D hadj).2.1; linarith [hP, this]
    have hUyp : 0 < (stepU D y x : ℝ) := by
      have := (stepU_prime D hadj).2.1; linarith [hP, this]
    have hrel := (step_rel D hC hL hP hadj hp2).symm hC' (div_pos hL hVyp) (div_pos hL hUyp)
    rw [← hsw1, ← hsw2] at hrel
    exact hrel

lemma PolyRel.congr {k : ℕ} {C δ : ℝ} {x₁ L₁ x₂ L₂ x₁' L₁' x₂' L₂' : ℝ}
    {P₁ P₂ P₁' P₂' : ℝ[X]}
    (h : PolyRel k C δ x₁ L₁ P₁ x₂ L₂ P₂)
    (hx₁ : x₁' = x₁) (hL₁ : L₁' = L₁) (hP₁ : P₁' = P₁)
    (hx₂ : x₂' = x₂) (hL₂ : L₂' = L₂) (hP₂ : P₂' = P₂) :
    PolyRel k C δ x₁' L₁' P₁' x₂' L₂' P₂' := by
  rw [hx₁, hL₁, hP₁, hx₂, hL₂, hP₂]
  exact h

theorem bike_adi_side {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : Work.BMF.QuadData k f c C X L P₁ P₂)
    (hC : 0 < C) (hP : 0 < P₁) (hL : 0 < L)
    (hbig : 8000 * P₁ ^ 2 < X / L)
    (hL1 : 1 ≤ L / (2 * P₁))
    (hLbig : 2 * Work.BMF.symmConst k (max C (Work.BMF.symmConst k C)) * ((k : ℝ) + 1) *
        (k : ℝ) ^ k * (k.factorial : ℝ) < L / (2 * P₁))
    {ℓ : ℕ} {x : ℝ} {W : Fin (ℓ + 1) → Work.BMF.GVert D}
    (hW : W ∈ Work.BMF.closedWalkAll D ℓ x)
    {S : Finset ℕ} (hSne : S.Nonempty) (hSprime : ∀ p ∈ S, p.Prime)
    (hstep : ∀ p ∈ S, ∀ j : Fin ℓ, p ∈ Work.BMF.stepS D (W j.castSucc) (W j.succ) ∨
      p ∈ Work.BMF.stepS D (W j.succ) (W j.castSucc)) :
    Work.BMF.PolyRel k
      (Work.BMF.cycConst k (Work.BMF.symmConst k (max C (Work.BMF.symmConst k C))) ℓ)
      (1 / ((S.prod (fun p => p) : ℕ) : ℝ))
      (x / ((Work.BMF.walkProdV D ℓ W : ℕ) : ℝ)) (L / ((Work.BMF.walkProdV D ℓ W : ℕ) : ℝ))
        (Work.BMF.dil ((Work.BMF.walkProdV D ℓ W : ℕ) : ℝ) (D.pol x))
      (x / ((Work.BMF.walkProdU D ℓ W : ℕ) : ℝ)) (L / ((Work.BMF.walkProdU D ℓ W : ℕ) : ℝ))
        (Work.BMF.dil ((Work.BMF.walkProdU D ℓ W : ℕ) : ℝ) (D.pol x)) := by
  classical
  obtain ⟨hWwalk, hWlast, hW0⟩ := Finset.mem_filter.mp hW
  obtain ⟨_, hadj⟩ := Finset.mem_filter.mp hWwalk
  obtain ⟨p₀, hp₀S⟩ := hSne
  have hSne' : S.Nonempty := ⟨p₀, hp₀S⟩
  set C'' : ℝ := symmConst k (max C (symmConst k C)) with hC''def
  have hC'pos : 0 < max C (symmConst k C) := lt_of_lt_of_le hC (le_max_left _ _)
  have hC''pos : 0 < C'' := by rw [hC''def]; exact symmConst_pos hC'pos
  have hC''le1 : 1 ≤ C'' := by
    rw [hC''def, symmConst]
    have hG : 0 ≤ ((k : ℝ) + 1) * ((k : ℝ) * (2 * max C (symmConst k C) + 1) + 1) ^ k := by
      positivity
    have hC0 : 0 ≤ max C (symmConst k C) := hC'pos.le
    nlinarith [hC0, hG, mul_nonneg hC0 hG, mul_nonneg (mul_nonneg hC0 hC0) hG]
  set δ : ℝ := 1 / ((S.prod (fun p => p) : ℕ) : ℝ) with hδ
  set V : Fin ℓ → ℕ := fun j => stepV D (W j.castSucc) (W j.succ) with hV
  set U : Fin ℓ → ℕ := fun j => stepU D (W j.castSucc) (W j.succ) with hU
  have hVprime : ∀ j : Fin ℓ, IsPrimeIn P₁ (2 * P₁) (V j) := by
    intro j
    rcases hstep p₀ hp₀S j with h | h
    · simpa only [hV] using stepV_prime D (GAdjQ_of_mem_stepS D h)
    · simpa only [hV] using stepV_prime D
        ((GAdjQ_symm D p₀ (W j.succ) (W j.castSucc)).mp (GAdjQ_of_mem_stepS D h))
  have hUprime : ∀ j : Fin ℓ, IsPrimeIn P₁ (2 * P₁) (U j) := by
    intro j
    rcases hstep p₀ hp₀S j with h | h
    · simpa only [hU] using stepU_prime D (GAdjQ_of_mem_stepS D h)
    · simpa only [hU] using stepU_prime D
        ((GAdjQ_symm D p₀ (W j.succ) (W j.castSucc)).mp (GAdjQ_of_mem_stepS D h))
  have hVpos : ∀ j, 0 < V j := fun j => (hVprime j).1.pos
  have hUpos : ∀ j, 0 < U j := fun j => (hUprime j).1.pos
  obtain ⟨hcf0, hcfl, haaV1, haaV2, hcfpos, haaVpos⟩ := cycFac_basic ℓ V U hVpos hUpos
  set xv : Fin (ℓ + 1) → ℝ := fun i => (W i).1 / ((cycFac ℓ V U i.val : ℕ) : ℝ) with hxv
  set Lv : Fin (ℓ + 1) → ℝ := fun i => L / ((cycFac ℓ V U i.val : ℕ) : ℝ) with hLv
  set Pv : Fin (ℓ + 1) → ℝ[X] := fun i => dil ((cycFac ℓ V U i.val : ℕ) : ℝ) (D.pol (W i).1)
    with hPv
  have hLvpos : ∀ i, 0 < Lv i := by
    intro i
    have h0 : (0:ℝ) < ((cycFac ℓ V U i.val : ℕ) : ℝ) := by
      have := hcfpos i.val; positivity
    exact div_pos hL h0
  have hstep' : ∀ j : Fin ℓ, PolyRel k C'' δ (xv j.castSucc) (Lv j.castSucc) (Pv j.castSucc)
      (xv j.succ) (Lv j.succ) (Pv j.succ) := by
    intro j
    have hVle : (V j : ℝ) ≤ 2 * P₁ := (hVprime j).2.2
    have hVposj : 0 < (V j : ℝ) := by
      have h2 : (2 : ℝ) ≤ (V j : ℝ) := by exact_mod_cast (hVprime j).1.two_le
      linarith
    have hcrt : PolyRel k C'' δ
        ((W j.castSucc).1 / (V j : ℝ)) (L / (V j : ℝ)) (dil (V j : ℝ) (D.pol (W j.castSucc).1))
        ((W j.succ).1 / (U j : ℝ)) (L / (U j : ℝ)) (dil (U j : ℝ) (D.pol (W j.succ).1)) := by
      refine polyRel_crt hC''pos hSne' hSprime ?_ ?_ ?_
      · rw [le_div_iff₀ hVposj]
        have h2 : 2 * P₁ ≤ L := by
          have h := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * P₁)).mp hL1
          simpa using h
        linarith
      · have hGlt : 2 * C'' * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) < L / (2 * P₁) := by
          rw [hC''def]; exact hLbig
        rw [lt_div_iff₀ hVposj]
        have h1 : 2 * C'' * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) * (2 * P₁) < L := by
          have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * P₁)).mp hGlt
          linarith
        have hG0 : 0 ≤ 2 * C'' * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) := by
          have hk1 : (0:ℝ) ≤ (k : ℝ) + 1 := by positivity
          have hkk : (0:ℝ) ≤ (k : ℝ) ^ k := by positivity
          have hkf : (0:ℝ) ≤ (k.factorial : ℝ) := by positivity
          positivity
        have hmono : 2 * C'' * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) * (V j)
            ≤ 2 * C'' * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) * (2 * P₁) :=
          mul_le_mul_of_nonneg_left hVle hG0
        linarith
      · intro p hpS
        have hp' := polyRel_step_mem D hC hP hL hbig (hadj j) (hstep p hpS j)
        simpa only [hV, hU] using hp'
    have hγpos : 0 < ((aaV ℓ V U j : ℕ) : ℝ) := by
      have := haaVpos j; positivity
    have hdil := hcrt.dilate hγpos
    have hspar := hdil.sparsify (aaV ℓ V U j)
    have hδγ : ((aaV ℓ V U j : ℕ) : ℝ) * (δ / ((aaV ℓ V U j : ℕ) : ℝ)) = δ := by
      have hne : ((aaV ℓ V U j : ℕ) : ℝ) ≠ 0 := ne_of_gt hγpos
      field_simp
    rw [hδγ] at hspar
    have hcyc1 : ((cycFac ℓ V U j.val : ℕ) : ℝ) = ((aaV ℓ V U j : ℕ) : ℝ) * ((V j : ℕ) : ℝ) := by
      rw [← haaV1 j]; push_cast; ring
    have hcyc2 : ((cycFac ℓ V U (j.val + 1) : ℕ) : ℝ) = ((aaV ℓ V U j : ℕ) : ℝ) * ((U j : ℕ) : ℝ) := by
      rw [← haaV2 j]; push_cast; ring
    have hx1eq : (W j.castSucc).1 / ((cycFac ℓ V U j.val : ℕ) : ℝ)
        = (W j.castSucc).1 / (V j : ℝ) / ((aaV ℓ V U j : ℕ) : ℝ) := by
      rw [hcyc1, div_div, mul_comm]
    have hL1eq : L / ((cycFac ℓ V U j.val : ℕ) : ℝ)
        = L / (V j : ℝ) / ((aaV ℓ V U j : ℕ) : ℝ) := by
      rw [hcyc1, div_div, mul_comm]
    have hP1eq : dil ((cycFac ℓ V U j.val : ℕ) : ℝ) (D.pol (W j.castSucc).1)
        = dil ((aaV ℓ V U j : ℕ) : ℝ) (dil (V j : ℝ) (D.pol (W j.castSucc).1)) := by
      rw [hcyc1, ← dil_mul]
    have hx2eq : (W j.succ).1 / ((cycFac ℓ V U (j.val + 1) : ℕ) : ℝ)
        = (W j.succ).1 / (U j : ℝ) / ((aaV ℓ V U j : ℕ) : ℝ) := by
      rw [hcyc2, div_div, mul_comm]
    have hL2eq : L / ((cycFac ℓ V U (j.val + 1) : ℕ) : ℝ)
        = L / (U j : ℝ) / ((aaV ℓ V U j : ℕ) : ℝ) := by
      rw [hcyc2, div_div, mul_comm]
    have hP2eq : dil ((cycFac ℓ V U (j.val + 1) : ℕ) : ℝ) (D.pol (W j.succ).1)
        = dil ((aaV ℓ V U j : ℕ) : ℝ) (dil (U j : ℝ) (D.pol (W j.succ).1)) := by
      rw [hcyc2, ← dil_mul]
    have hspar2 : PolyRel k C'' δ
        ((W j.castSucc).1 / ((cycFac ℓ V U j.val : ℕ) : ℝ))
          (L / ((cycFac ℓ V U j.val : ℕ) : ℝ))
          (dil ((cycFac ℓ V U j.val : ℕ) : ℝ) (D.pol (W j.castSucc).1))
        ((W j.succ).1 / ((cycFac ℓ V U (j.val + 1) : ℕ) : ℝ))
          (L / ((cycFac ℓ V U (j.val + 1) : ℕ) : ℝ))
          (dil ((cycFac ℓ V U (j.val + 1) : ℕ) : ℝ) (D.pol (W j.succ).1)) :=
      hspar.congr hx1eq hL1eq hP1eq hx2eq hL2eq hP2eq
    simpa only [hxv, hLv, hPv, Fin.val_castSucc, Fin.val_succ] using hspar2
  have hmain := polyrel_chain_ind k C'' δ hC''le1 ℓ xv Lv Pv hLvpos hstep'
  have hcycf0' : cycFac ℓ V U 0 = walkProdV D ℓ W := by
    rw [hcf0]
    simp only [walkProdV]
    exact Finset.prod_congr rfl (fun j _ => by simp only [hV])
  have hcycf0 : ((cycFac ℓ V U 0 : ℕ) : ℝ) = ((walkProdV D ℓ W : ℕ) : ℝ) := by rw [hcycf0']
  have hcycfl' : cycFac ℓ V U ℓ = walkProdU D ℓ W := by
    rw [hcfl]
    simp only [walkProdU]
    exact Finset.prod_congr rfl (fun j _ => by simp only [hU])
  have hcycfl : ((cycFac ℓ V U ℓ : ℕ) : ℝ) = ((walkProdU D ℓ W : ℕ) : ℝ) := by rw [hcycfl']
  have hlastW : (W (Fin.last ℓ)).1 = x := by
    have h1 : W (Fin.last ℓ) = W 0 := by
      rw [show Fin.last ℓ = (⟨ℓ, Nat.lt_succ_self ℓ⟩ : Fin (ℓ + 1)) from Fin.ext rfl]
      exact hWlast
    rw [h1, hW0]
  have hx0 : xv 0 = x / ((walkProdV D ℓ W : ℕ) : ℝ) := by
    simp only [hxv, Fin.val_zero]
    rw [hcycf0, hW0]
  have hLv0 : Lv 0 = L / ((walkProdV D ℓ W : ℕ) : ℝ) := by
    simp only [hLv, Fin.val_zero]
    rw [hcycf0]
  have hPv0 : Pv 0 = dil ((walkProdV D ℓ W : ℕ) : ℝ) (D.pol x) := by
    simp only [hPv, Fin.val_zero]
    rw [hcycf0, hW0]
  have hxl : xv (Fin.last ℓ) = x / ((walkProdU D ℓ W : ℕ) : ℝ) := by
    simp only [hxv, Fin.val_last]
    rw [hcycfl, hlastW]
  have hLvl : Lv (Fin.last ℓ) = L / ((walkProdU D ℓ W : ℕ) : ℝ) := by
    simp only [hLv, Fin.val_last]
    rw [hcycfl]
  have hPvl : Pv (Fin.last ℓ) = dil ((walkProdU D ℓ W : ℕ) : ℝ) (D.pol x) := by
    simp only [hPv, Fin.val_last]
    rw [hcycfl, hlastW]
  rw [hx0, hLv0, hPv0, hxl, hLvl, hPvl] at hmain
  simpa only [hδ, hC''def] using hmain

end Work.BMF
