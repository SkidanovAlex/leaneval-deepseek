import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstFreezeDefs
import Submission.Work.BourgainPlan.Maximal.opMul_modSeq
import Submission.Work.BourgainPlan.Maximal.opMul_index_add

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

open Work.BourgainPlan.IonescuWainger

set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

/-! ## Elementary facts about `opMul`

The multiplier `opMul Φ f hf` depends only on the *function* `f` (through `ftLp`), and it is
additive and `ℂ`-homogeneous in that argument (`ftLp_add`, `ftLp_smul` of
`Work.BourgainPlan.IonescuWainger.OpMulLinear`, transported across `ftLp_injective`).  The
finset-sum form `opMul_eq_sum_lc` is what allows the modulated input `mstModSeq G E f x` to be
decomposed over the arcs of the level. -/

/-- The zero sequence is `ℓ²`. -/
theorem memℓp_zero_two : Memℓp (0 : ℤ → ℂ) 2 := by
  rw [Memℓp]; norm_num

/-- The multiplier with any symbol applied to the zero sequence is zero. -/
theorem opMul_zero_input (Φ : Lp ℂ ⊤ mstHaar) : opMul Φ (0 : ℤ → ℂ) memℓp_zero_two = 0 := by
  funext n
  rw [opMul_apply, opMulLp]
  have h0 : (ftLp (0 : ℤ → ℂ) memℓp_zero_two : Lp ℂ 2 mstHaar) = 0 := by
    rw [ftLp]; exact map_zero _
  rw [h0]; simp

/-- `opMul` depends only on the sequence, not on the proof of `Memℓp`. -/
theorem opMul_congr_input (Φ : Lp ℂ ⊤ mstHaar) {f g : ℤ → ℂ} (h : f = g) (hf : Memℓp f 2)
    (hg : Memℓp g 2) : opMul Φ f hf = opMul Φ g hg := by
  subst h; rfl

/-- `opMul` is additive in its sequence argument. -/
theorem opMul_add_input (Φ : Lp ℂ ⊤ mstHaar) (f g : ℤ → ℂ) (hf : Memℓp f 2) (hg : Memℓp g 2) :
    opMul Φ (f + g) (hf.add hg) = opMul Φ f hf + opMul Φ g hg := by
  apply ftLp_injective (opMul_memℓp Φ (f+g) (hf.add hg))
    ((opMul_memℓp Φ f hf).add (opMul_memℓp Φ g hg))
  rw [ftLp_opMul, ftLp_add (opMul_memℓp Φ f hf) (opMul_memℓp Φ g hg), ftLp_opMul, ftLp_opMul]
  show Φ • ftLp (f + g) _ = Φ • ftLp f hf + Φ • ftLp g hg
  rw [ftLp_add hf hg, Lp.add_smul]

/-- `opMul` is `ℂ`-homogeneous in its sequence argument. -/
theorem opMul_smul_input (Φ : Lp ℂ ⊤ mstHaar) (c : ℂ) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    opMul Φ (c • f) (hf.const_smul c) = c • opMul Φ f hf := by
  apply ftLp_injective (opMul_memℓp Φ (c • f) (hf.const_smul c))
    ((opMul_memℓp Φ f hf).const_smul c)
  rw [ftLp_opMul, ftLp_smul c (opMul_memℓp Φ f hf), ftLp_opMul]
  show Φ • ftLp (c • f) _ = c • (Φ • ftLp f hf)
  rw [ftLp_smul c hf, Lp.smul_comm]

/-- **`opMul` is linear in its sequence argument**, in the form needed for the freezing
identity: if `G` agrees pointwise with the finite linear combination `Σ_{i∈s} c i * g i k`, then
`opMul Φ G hG` is the corresponding linear combination `Σ_{i∈s} c i • opMul Φ (g i) (hg i)`. -/
theorem opMul_eq_sum_lc {ι : Type*} (Φ : Lp ℂ ⊤ mstHaar) (s : Finset ι) (c : ι → ℂ)
    (g : ι → ℤ → ℂ) (hg : ∀ i, Memℓp (g i) 2) :
    ∀ (G : ℤ → ℂ) (hG : Memℓp G 2),
      (∀ k, G k = ∑ i ∈ s, c i * g i k) →
      opMul Φ G hG = ∑ i ∈ s, c i • opMul Φ (g i) (hg i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro G hG hGeq
      have hG0 : G = 0 := by funext k; rw [hGeq k]; simp
      rw [opMul_congr_input Φ hG0 hG memℓp_zero_two, opMul_zero_input, Finset.sum_empty]
  | insert a s ha ih =>
      intro G hG hGeq
      have hGeq' : ∀ k, G k = c a * g a k + ∑ i ∈ s, c i * g i k := by
        intro k; rw [hGeq k, Finset.sum_insert ha]
      have hS : Memℓp (G - c a • g a) 2 := hG.sub ((hg a).const_smul (c a))
      have hSeq : ∀ k, (G - c a • g a) k = ∑ i ∈ s, c i * g i k := by
        intro k; rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hGeq' k]; ring
      have hsplit : G = c a • g a + (G - c a • g a) := by
        funext k; simp [Pi.add_apply]
      rw [opMul_congr_input Φ hsplit hG (((hg a).const_smul (c a)).add hS)]
      rw [opMul_add_input Φ (c a • g a) (G - c a • g a) ((hg a).const_smul (c a)) hS]
      rw [opMul_smul_input Φ (c a) (g a) (hg a)]
      rw [ih (G - c a • g a) hS hSeq]
      rw [Finset.sum_insert ha]

/-- Additivity of `opMul` in its symbol, at a point. -/
theorem opMul_smul_apply (c : ℂ) (Φ : Lp ℂ ⊤ mstHaar) (f : ℤ → ℂ) (hf : Memℓp f 2) (y : ℤ) :
    opMul (c • Φ) f hf y = c * opMul Φ f hf y := by
  have h := congrFun (opMul_smul c Φ f hf) y
  rwa [Pi.smul_apply, smul_eq_mul] at h

/-- Subtracting two multipliers is multiplying by the difference of the symbols, at a point. -/
theorem opMul_sub_apply (Φ Ψ : Lp ℂ ⊤ mstHaar) (f : ℤ → ℂ) (hf : Memℓp f 2) (y : ℤ) :
    opMul Φ f hf y - opMul Ψ f hf y = opMul (Φ - Ψ) f hf y := by
  have h := congrFun (opMul_sub Φ Ψ f hf) y
  rwa [Pi.sub_apply] at h

/-- `opMul` depends only on the a.e. class of the symbol, at a point. -/
theorem opMul_congr_ae_apply {Φ Ψ : Lp ℂ ⊤ mstHaar} (h : Φ =ᵐ[haarT] Ψ) (f : ℤ → ℂ)
    (hf : Memℓp f 2) (y : ℤ) : opMul Φ f hf y = opMul Ψ f hf y := by
  rw [opMul_congr_ae h f hf]

/-- **`opMul` applied to a modulated sequence, at a point**: the modulation is transferred from
the input to the output (`opMul_modSeq`). -/
theorem opMul_modSeq_apply (Φ : Lp ℂ ⊤ mstHaar) (f : ℤ → ℂ) (hf : Memℓp f 2) (α : Circ) (y : ℤ) :
    opMul Φ (modSeq f α) (memℓp_modSeq hf α) y
      = opMul (mstArcTransLp α Φ) f hf y * fourier y α := by
  have h := congrFun (opMul_modSeq Φ f hf α) y
  rwa [modSeq] at h

/-! ## The characters of the circle -/

/-- The character at the negated point is the conjugate character: `e_n(-x) = conj (e_n(x))`. -/
theorem fourier_neg_apply (n : ℤ) (x : Circ) : fourier n (-x) = star (fourier n x) := by
  rw [fourier_apply, smul_neg, fourier_neg']; rfl

/-- `star (fourier n (-x)) = fourier n x`. -/
theorem star_fourier_neg_apply (n : ℤ) (x : Circ) : star (fourier n (-x)) = fourier n x := by
  rw [fourier_neg_apply, star_star]

/-- **The character identity of the freezing step**: `star (fourier u (ξ-β)) = fourier u β *
star (fourier u ξ)`, i.e. `e(−u(ξ−β)) = e(uβ) · conj (e(uξ))`. -/
theorem star_fourier_sub (n : ℤ) (ξ β : Circ) :
    star (fourier n (ξ - β)) = fourier n β * star (fourier n ξ) := by
  rw [sub_eq_add_neg, fourier_add_right, star_mul, star_fourier_neg_apply]

/-! ## The freezing symbol -/

/-- **The symbol of the freezing difference is the class of the small symbol**: for any `L^∞`-class
`Φ` representing `φ = Φ_{2^n}ψ_s`, the class
`fourier u β • mstSymStarLp u (mstArcTransLp β Φ) - mstArcTransLp β Φ`
is a.e. equal to `mstFreezeSymLp P d χ η hη s n u β`, whose representative is
`ξ ↦ (star (fourier u (ξ−β)) - 1) · φ(ξ−β)`. -/
theorem mstFreezeSym_ae_eq (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (s n u : ℕ) (β : Circ) (Φ : Lp ℂ ⊤ mstHaar)
    (hΦ : Φ =ᵐ[haarT] mstProfBumpFun P d χ η s n) :
    (fourier (u : ℤ) β • mstSymStarLp (u : ℤ) (mstArcTransLp β Φ) - mstArcTransLp β Φ)
      =ᵐ[haarT] mstFreezeSymLp P d χ η hη s n u β := by
  have hmp : MeasurePreserving (fun ξ : Circ => ξ + (-β)) haarT haarT :=
    measurePreserving_add_right _ _
  have h4 : arcTranslate β (Φ : Circ → ℂ) =ᵐ[haarT] fun ξ => mstProfBumpFun P d χ η s n (ξ - β) := by
    have h := hmp.quasiMeasurePreserving.ae hΦ
    filter_upwards [h] with ξ hξ
    rw [arcTranslate_apply, sub_eq_add_neg, hξ]
  filter_upwards [Lp.coeFn_smul (fourier (u : ℤ) β) (mstSymStarLp (u : ℤ) (mstArcTransLp β Φ)),
    mstSymStarLp_coeFn (u : ℤ) (mstArcTransLp β Φ), mstArcTransLp_coeFn β Φ, h4,
    Lp.coeFn_sub (fourier (u : ℤ) β • mstSymStarLp (u : ℤ) (mstArcTransLp β Φ)) (mstArcTransLp β Φ),
    mstFreezeSymLp_coeFn P d χ η hη s n u β] with ξ h1 h2 h3 h4' h5 h6
  rw [h5, Pi.sub_apply, h1, Pi.smul_apply, smul_eq_mul, h2, h3, h4', h6]
  rw [mstFreezeSymFun_apply, star_fourier_sub]
  ring

/-! ## The freezing identity -/

/-- **The freezing identity of MST §4.3** (the `x`-pointwise form).  For the level-`s` model at scale `2^n` — the multiplier with symbol `φ = Φ_{2^n}ψ_s` (`mstProfBumpFun`) applied to the modulated input `mstModSeq G (mstLvl l s) f x` — the difference between the values of the *frozen* model at `x+u` and at `x` is a sum of single multipliers over the arcs `β ∈ mstLvl l s` with the *small* symbols `mstFreezeSymFun P d χ η s n u β = (star (fourier u (·-β)) - 1)·φ(·-β)`.

Route (all named objects are in `Submission.Work.BourgainPlan.Maximal.mstFreezeDefs`; the two structural ingredients are `opMul_modSeq` and `opMul_index_add` from `Submission.Work.BourgainPlan.Maximal.opMul_modSeq` / `...opMul_index_add`, already proved):
1. replace `hB n` by the class of `φ` using `hModel` (`Lp.ext`, `mstProfBumpLp_coeFn`) and `opMul_congr_ae`;
2. write `mstModSeq G E f x = Σ_{β∈E} (G β * fourier (-x) β) • modSeq f β` pointwise (`mstModSeq_apply`, `mstArc_apply`, `modSeq`, `fourier_add`/`fourier_sub`: `fourier (k-x) β = fourier k β * fourier (-x) β`), and use that `opMul` is additive/homogeneous in its *input* (`ftLp_add`/`ftLp_smul` from `Work.BourgainPlan.IonescuWainger.OpMulLinear` + `ftLp_opMul`);
3. `opMul_modSeq` at `y = x` gives `opMul (mstProfBumpLp …) (modSeq f β) _ x = fourier x β * opMul (mstArcTransLp β Φ) f hf x`, hence `(G β fourier(-x)β)·fourier x β = G β` contributes the bare weight;
4. `opMul_index_add` turns the pair of values at `x+u` and `x` into a single multiplier: `opMul ((fourier u β) • mstSymStarLp u (mstArcTransLp β Φ) - mstArcTransLp β Φ) f hf x` (`opMul_sub` and scalar multiples of `Lp` classes: `opMul Φ f hf - c • opMul Ψ f hf = opMul (Φ - c • Ψ) f hf`), whose representative function is `ξ ↦ (fourier u β·star (fourier u ξ) - 1)·φ(ξ-β)`;
5. the pointwise identity `fourier u β * star (fourier u ξ) = star (fourier u (ξ-β))` (`fourier_add_right`/`star_fourier_add_right` in `Work.BourgainPlan.Maximal.mstKernel_helpers`, or `fourier_add` + `star_mul`) identifies that class with `mstFreezeSymLp P d χ η hη s n u β` (`Lp.ext` + `mstFreezeSymLp_coeFn`) and `opMul_congr_ae` finishes. -/
theorem mstFreeze_diff_eq (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (s n u : ℕ) (G : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (f : ℤ → ℂ) (hf : Memℓp f 2)
    (hB : ∀ n : ℕ, MeasureTheory.Lp ℂ ⊤ Work.BourgainPlan.Maximal.mstHaar)
    (hModel : Work.BourgainPlan.Maximal.HasModel P d χ η s hB) (x : ℤ) :
    Work.BourgainPlan.IonescuWainger.opMul (hB n)
        (Work.BourgainPlan.Maximal.mstModSeq G (Work.BourgainPlan.Maximal.mstLvl l s) f x)
        (Work.BourgainPlan.Maximal.memℒp_mstModSeq hf x) (x + (u : ℤ))
      - Work.BourgainPlan.IonescuWainger.opMul (hB n)
        (Work.BourgainPlan.Maximal.mstModSeq G (Work.BourgainPlan.Maximal.mstLvl l s) f x)
        (Work.BourgainPlan.Maximal.memℒp_mstModSeq hf x) x
      = Finset.sum (Work.BourgainPlan.Maximal.mstLvl l s) (fun β =>
          G β * Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstFreezeSymLp P d χ η hη s n u β) f hf x) := by
  classical
  have hdec : ∀ y : ℤ, opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) y
      = ∑ β ∈ mstLvl l s,
          (G β * fourier (-x) β)
            * (fourier y β * opMul (mstArcTransLp β (hB n)) f hf y) := by
    intro y
    rw [opMul_eq_sum_lc (hB n) (mstLvl l s)
      (fun β => G β * fourier (-x) β) (fun β => modSeq f β) (fun β => memℓp_modSeq hf β)
      (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) ?_, Finset.sum_apply]
    · refine Finset.sum_congr rfl (fun β _ => ?_)
      rw [Pi.smul_apply, smul_eq_mul, opMul_modSeq_apply (hB n) f hf β y]
      ring
    · intro k
      rw [mstModSeq_apply, mstArc_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun β _ => ?_)
      have hc : fourier (-x) β * fourier k β = fourier (k - x) β := by
        rw [← fourier_add, show (-x) + k = (k - x : ℤ) from by ring]
      simp only [modSeq]
      rw [← hc]; ring_nf
  rw [hdec (x + (u : ℤ)), hdec x, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  have hb1 : fourier (-x) β * fourier (x + (u : ℤ)) β = fourier (u : ℤ) β := by
    rw [← fourier_add, show (-x) + (x + (u : ℤ)) = ((u : ℤ)) from by ring]
  have hb2 : fourier (-x) β * fourier x β = 1 := by
    rw [← fourier_add, show (-x) + x = ((0 : ℤ)) from by ring, fourier_zero]
  have hAB : (G β * fourier (-x) β)
        * (fourier (x + (u : ℤ)) β * opMul (mstArcTransLp β (hB n)) f hf (x + (u : ℤ)))
      = G β * (fourier (u : ℤ) β * opMul (mstArcTransLp β (hB n)) f hf (x + (u : ℤ))) := by
    rw [← hb1]; ring_nf
  have hBB : (G β * fourier (-x) β) * (fourier x β * opMul (mstArcTransLp β (hB n)) f hf x)
      = G β * opMul (mstArcTransLp β (hB n)) f hf x := by
    rw [show (G β * fourier (-x) β) * (fourier x β * opMul (mstArcTransLp β (hB n)) f hf x)
        = G β * (fourier (-x) β * fourier x β) * opMul (mstArcTransLp β (hB n)) f hf x
        from by ring_nf, hb2]
    ring_nf
  rw [hAB, hBB]
  have hA : opMul (mstArcTransLp β (hB n)) f hf (x + (u : ℤ))
      = opMul (mstSymStarLp (u : ℤ) (mstArcTransLp β (hB n))) f hf x :=
    opMul_index_add (mstArcTransLp β (hB n)) f hf (u : ℤ) x
  rw [hA]
  have hcomb : fourier (u : ℤ) β * opMul (mstSymStarLp (u : ℤ) (mstArcTransLp β (hB n))) f hf x
      = opMul (fourier (u : ℤ) β • mstSymStarLp (u : ℤ) (mstArcTransLp β (hB n))) f hf x :=
    (opMul_smul_apply (fourier (u : ℤ) β) (mstSymStarLp (u : ℤ) (mstArcTransLp β (hB n))) f hf x).symm
  rw [hcomb, ← mul_sub, opMul_sub_apply]
  rw [opMul_congr_ae_apply (mstFreezeSym_ae_eq P d χ η hη s n u β (hB n) (hModel n)) f hf x]

end

end Work.BourgainPlan.Maximal
