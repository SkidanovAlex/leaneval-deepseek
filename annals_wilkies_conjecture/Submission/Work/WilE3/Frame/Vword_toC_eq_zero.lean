import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.Vcoef
import Submission.Work.WilE3.Frame.Vdir_Vword
import Submission.Work.WilE3.Frame.detOp_opMono_prepend
import Submission.Work.WilE3.Frame.eaEvalC_toC

namespace Work.WilE3.Frame

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E
open Work.WilE3 (jacDet)

variable {k r j : ℕ}

/-! ## §0. Two ingredients: analyticity of the frame coefficients, and the Leibniz rule for `Vdir` -/

lemma analyticAt_jacValC (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (z : Fin k → ℂ) : AnalyticAt ℂ (jacValC c h ι) z :=
  (Work.WilE3.API.eaEvalC_fderiv_analytic c (jacDet c h ι) z).1

lemma eventually_jacValC_ne_zero (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    {z : Fin k → ℂ} (hz : jacValC c h ι z ≠ 0) :
    ∀ᶠ w in 𝓝 z, jacValC c h ι w ≠ 0 :=
  (analyticAt_jacValC c h ι z).continuousAt.eventually_ne hz

/-- The coordinates of the tangential frame vector are complex-analytic wherever the `ι`-Jacobian
`jacValC` does not vanish.  The only non-polynomial ingredient is `(jacValC ·)⁻¹`; the entries of
`(jacMatC ·).adjugate` are analytic because `jacMatC c h ι w` is the `ℂ`-image of the *fixed*
polynomial matrix `M = (eaD c (ι b) (h a))` under the ring homomorphism `Q ↦ eaEvalC c Q w`, and
adjugates commute with ring homomorphisms (`RingHom.map_adjugate`). -/
lemma analyticAt_VcoefC' (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) {z : Fin k → ℂ} (hz : jacValC c h ι z ≠ 0) (i : Fin k) :
    AnalyticAt ℂ (fun w => VcoefC c h ι l w i) z := by
  set M : Matrix (Fin j) (Fin j) (EAPoly k r) := Matrix.of fun a b => eaD c (ι b) (h a) with hMdef
  have hadj : ∀ a b : Fin j, AnalyticAt ℂ (fun w => (jacMatC c h ι w).adjugate a b) z := by
    intro a b
    have hfun : (fun w => (jacMatC c h ι w).adjugate a b)
        = fun w => Work.WilE3.eaEvalC c (M.adjugate a b) w := by
      funext w
      have h1 : jacMatC c h ι w
          = (MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) (Work.WilE3.API.eaPsi c w)).mapMatrix M := by
        ext a' b'
        simp only [jacMatC, Matrix.of_apply, hMdef]
        exact Work.WilE3.API.eaEvalC_eq c (eaD c (ι b') (h a')) w
      rw [h1, ← RingHom.map_adjugate, RingHom.mapMatrix_apply]
      exact (Work.WilE3.API.eaEvalC_eq c (M.adjugate a b) w).symm
    rw [hfun]
    exact (Work.WilE3.API.eaEvalC_fderiv_analytic c (M.adjugate a b) z).1
  have hbeta : ∀ b : Fin j, AnalyticAt ℂ (fun w => betaC c h ι l w b) z := by
    intro b
    have hfun : (fun w => betaC c h ι l w b)
        = fun w => (jacValC c h ι w)⁻¹ *
            ∑ a, (jacMatC c h ι w).adjugate b a * dlColC c h l w a := by
      funext w
      simp only [betaC, Matrix.mulVec, dotProduct]
    rw [hfun]
    rw [show (fun w => (jacValC c h ι w)⁻¹ *
          ∑ a, (jacMatC c h ι w).adjugate b a * dlColC c h l w a)
        = (fun w => (jacValC c h ι w)⁻¹)
          * (∑ a : Fin j, fun w => (jacMatC c h ι w).adjugate b a * dlColC c h l w a) from by
      funext w
      simp only [Pi.mul_apply, Finset.sum_apply]]
    refine ((analyticAt_jacValC c h ι z).inv hz).mul (Finset.analyticAt_sum _ (fun a _ => ?_))
    exact (hadj b a).mul
      ((Work.WilE3.API.eaEvalC_fderiv_analytic c (eaD c l (h a)) z).1)
  have hterm : ∀ b : Fin j, AnalyticAt ℂ
      (fun w => if ι b = i then betaC c h ι l w b else 0) z := by
    intro b
    by_cases hb : ι b = i
    · simp only [hb, ite_true]; exact hbeta b
    · simp only [hb, ite_false]; exact analyticAt_const
  have hfun : (fun w => VcoefC c h ι l w i) = fun w =>
      (if i = l then (1 : ℂ) else 0) - ∑ b, (if ι b = i then betaC c h ι l w b else 0) := by
    funext w; rfl
  rw [hfun]
  rw [show (fun w => (if i = l then (1 : ℂ) else 0)
        - ∑ b, (if ι b = i then betaC c h ι l w b else 0))
      = (fun _ : Fin k → ℂ => (if i = l then (1 : ℂ) else 0))
        - (∑ b : Fin j, fun w => if ι b = i then betaC c h ι l w b else 0) from by
    funext w
    simp only [Pi.sub_apply, Finset.sum_apply]]
  exact analyticAt_const.sub (Finset.analyticAt_sum _ (fun b _ => hterm b))

/-- The Leibniz rule plus linearity for `Vdir` in the shape the induction consumes it.  All the
functions involved are analytic at `z₀`, hence differentiable on a neighbourhood of `z₀`; there
`fderiv` is additive and satisfies the product rule, and the remaining step is bookkeeping in
`Finset.sum`. -/
lemma Vdir_sum_mul' (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (K : ℕ) (g E : Fin K → (Fin k → ℂ) → ℂ) (z₀ : Fin k → ℂ)
    (hg : ∀ i, AnalyticAt ℂ (g i) z₀) (hE : ∀ i, AnalyticAt ℂ (E i) z₀) :
    Vdir c h ι l (fun z => ∑ i, g i z * E i z) =ᶠ[𝓝 z₀]
      (fun z => ∑ i, (Vdir c h ι l (g i) z * E i z + g i z * Vdir c h ι l (E i) z)) := by
  have hgd : ∀ i : Fin K, ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ (g i) z := fun i => by
    obtain ⟨p, hp⟩ := hg i
    exact hp.eventually_differentiableAt
  have hEd : ∀ i : Fin K, ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ (E i) z := fun i => by
    obtain ⟨p, hp⟩ := hE i
    exact hp.eventually_differentiableAt
  have hall : ∀ᶠ z in 𝓝 z₀, (∀ i, DifferentiableAt ℂ (g i) z) ∧
      (∀ i, DifferentiableAt ℂ (E i) z) :=
    Filter.Eventually.and (Filter.eventually_all.2 hgd) (Filter.eventually_all.2 hEd)
  filter_upwards [hall] with z hz
  have hdz : ∀ i : Fin K, DifferentiableAt ℂ (fun w => g i w * E i w) z :=
    fun i => (hz.1 i).mul (hz.2 i)
  have hsingle : ∀ (i : Fin K) (i' : Fin k), fderiv ℂ (fun w => g i w * E i w) z (Pi.single i' 1)
      = g i z * fderiv ℂ (E i) z (Pi.single i' 1)
        + E i z * fderiv ℂ (g i) z (Pi.single i' 1) := by
    intro i i'
    rw [show (fun w => g i w * E i w) = g i * E i from rfl]
    rw [fderiv_mul (hz.1 i) (hz.2 i)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  simp only [Vdir]
  rw [show (fun z => ∑ i, g i z * E i z) = ∑ i : Fin K, fun w => g i w * E i w from by
    funext z
    simp only [Finset.sum_apply]]
  rw [fderiv_sum (u := Finset.univ) (A := fun i => fun w => g i w * E i w) (fun i _ => hdz i)]
  simp only [_root_.sum_apply, hsingle]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (∑ i', VcoefC c h ι l z i' *
        (g i z * fderiv ℂ (E i) z (Pi.single i' 1) + E i z * fderiv ℂ (g i) z (Pi.single i' 1)))
      = (∑ i', VcoefC c h ι l z i' * (g i z * fderiv ℂ (E i) z (Pi.single i' 1)))
        + ∑ i', VcoefC c h ι l z i' * (E i z * fderiv ℂ (g i) z (Pi.single i' 1)) from by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i' _ => mul_add _ _ _]
  rw [show (∑ i', VcoefC c h ι l z i' * (E i z * fderiv ℂ (g i) z (Pi.single i' 1)))
      = (∑ i', VcoefC c h ι l z i' * fderiv ℂ (g i) z (Pi.single i' 1)) * E i z from by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i' _ => by ring]
  rw [show (∑ i', VcoefC c h ι l z i' * (g i z * fderiv ℂ (E i) z (Pi.single i' 1)))
      = ∑ i', g i z * (VcoefC c h ι l z i' * fderiv ℂ (E i) z (Pi.single i' 1)) from
    Finset.sum_congr rfl fun i' _ => by ring]
  ring

/-! ## §1. The frame identity on evaluated polynomials -/

lemma fderiv_eaEvalC_single (c : EAChain k r) (Q : EAPoly k r) (z : Fin k → ℂ) (i : Fin k) :
    fderiv ℂ (fun w => Work.WilE3.eaEvalC c Q w) z (Pi.single i 1)
      = Work.WilE3.eaEvalC c (eaD c i Q) z := by
  rw [(Work.WilE3.API.eaEvalC_fderiv_analytic c Q z).2.fderiv]
  simp only [_root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma Vdir_eaEvalC (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) {z : Fin k → ℂ} (hz : jacValC c h ι z ≠ 0) (Q : EAPoly k r) :
    Vdir c h ι l (fun w => Work.WilE3.eaEvalC c Q w) z
      = (jacValC c h ι z)⁻¹ * Work.WilE3.eaEvalC c (detOp c h ι l Q) z := by
  have hc : ∀ i : Fin k, VcoefC c h ι l z i * fderiv ℂ (fun w => Work.WilE3.eaEvalC c Q w) z
        (Pi.single i 1)
      = VcoefC c h ι l z i * Work.WilE3.eaEvalC c (eaD c i Q) z :=
    fun i => by rw [fderiv_eaEvalC_single]
  have hkey : (jacValC c h ι z)⁻¹ * Work.WilE3.eaEvalC c (detOp c h ι l Q) z
      = (jacValC c h ι z)⁻¹ * (jacValC c h ι z *
          ∑ i, VcoefC c h ι l z i * Work.WilE3.eaEvalC c (eaD c i Q) z) := by
    rw [eaEvalC_detOp_eq c h ι l z hz Q]
  rw [Vdir, Finset.sum_congr rfl (fun i _ => hc i), hkey, ← mul_assoc, inv_mul_cancel₀ hz,
    one_mul]

/-! ## §2. Analyticity and germ closure of `Vdir` -/

theorem analyticAt_Vdir' (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) {z : Fin k → ℂ} (hz : jacValC c h ι z ≠ 0) {G : (Fin k → ℂ) → ℂ}
    (hG : AnalyticAt ℂ G z) : AnalyticAt ℂ (Vdir c h ι l G) z := by
  have hf : ∀ i : Fin k, AnalyticAt ℂ (fun w => fderiv ℂ G w (Pi.single i 1)) z := by
    intro i
    have h1 : AnalyticAt ℂ (fderiv ℂ G) z := AnalyticAt.fderiv hG
    have h2 : AnalyticAt ℂ (fun L : (Fin k → ℂ) →L[ℂ] ℂ => L (Pi.single i 1))
        (fderiv ℂ G z) :=
      ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.apply ℂ (E := Fin k → ℂ) ℂ (Pi.single i 1)) (fderiv ℂ G z)
    exact h2.comp h1
  have hfun : Vdir c h ι l G
      = ∑ i : Fin k, fun w => VcoefC c h ι l w i * fderiv ℂ G w (Pi.single i 1) := by
    funext w
    simp only [Vdir, Finset.sum_apply]
  rw [hfun]
  exact Finset.analyticAt_sum _ (fun i _ => (analyticAt_VcoefC' c h ι l hz i).mul (hf i))

lemma Vdir_congr (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (l : Fin k)
    {F G : (Fin k → ℂ) → ℂ} {z : Fin k → ℂ} (hFG : F =ᶠ[𝓝 z] G) :
    Vdir c h ι l F =ᶠ[𝓝 z] Vdir c h ι l G := by
  have hd : fderiv ℂ F =ᶠ[𝓝 z] fderiv ℂ G := Filter.EventuallyEq.fderiv (𝕜 := ℂ) hFG
  filter_upwards [hd] with w hw
  simp only [Vdir]
  exact Finset.sum_congr rfl fun i _ => by rw [hw]

lemma eventuallyEq_sum_univ {α M : Type*} [AddCommMonoid M] {K : ℕ} {l : Filter α}
    {f g : Fin K → α → M} (h : ∀ i, f i =ᶠ[l] g i) :
    (fun x => ∑ i, f i x) =ᶠ[l] fun x => ∑ i, g i x := by
  have h' : ∀ᶠ x in l, ∀ i : Fin K, f i x = g i x := Filter.eventually_all.2 h
  filter_upwards [h'] with x hx
  exact Finset.sum_congr rfl fun i _ => hx i

lemma Vword_zero (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (F : (Fin k → ℂ) → ℂ) : Vword c h ι (0 : Fin k → ℕ) F = F := by
  have hL : ∀ L : List (Fin k), L.foldr (fun _ x => x) F = F := by
    intro L
    induction L with
    | nil => rfl
    | cons a t ih => simp
  unfold Vword
  simpa only [Pi.zero_apply, Function.iterate_zero_apply] using hL (List.finRange k)

/-! ## §3. The presentation of a frame word -/

def Pres (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (Q : EAPoly k r)
    (a : Fin k → ℂ) (ν : Fin k → ℕ) (F : (Fin k → ℂ) → ℂ) : Prop :=
  ∃ (K : ℕ) (g : Fin K → (Fin k → ℂ) → ℂ) (μ : Fin K → Fin k → ℕ),
    (∀ i, (∀ b, μ i (ι b) = 0) ∧ (∀ m, μ i m ≤ ν m)) ∧
      (∀ i, AnalyticAt ℂ (g i) a) ∧
      F =ᶠ[𝓝 a] fun z => ∑ i, g i z * Work.WilE3.eaEvalC c (opMono c h ι (μ i) Q) z

/-- The base case of the induction: the empty word presents `eaEvalC c f`. -/
lemma pres_zero (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (f : EAPoly k r) (a : Fin k → ℂ) :
    Pres c h ι f a 0 (Vword c h ι 0 (fun z => Work.WilE3.eaEvalC c f z)) := by
  have h0 : opMono c h ι (fun _ : Fin k => 0) f = f :=
    (Work.WilE3.API.opMono_basic c h ι (0 : Fin k → ℕ)).1 f
  refine ⟨1, fun _ _ => (1 : ℂ), fun _ _ => 0, ?_, ?_, ?_⟩
  · intro i
    exact ⟨fun b => rfl, fun m => Nat.zero_le _⟩
  · intro i; exact analyticAt_const
  · rw [Vword_zero]
    apply Filter.EventuallyEq.of_eq
    funext z
    simp only [Fin.sum_univ_one, h0, one_mul]

/-- **The frame word is a `C^ω`-combination of the ordered reduced derivatives.**  Every `V`-word
supported off `ι` is, near `a`, a finite sum of analytic functions times the evaluated `opMono`
words of multi-indices bounded by it.  The induction is on the order `∑ ν`; at each step the
smallest active index `l` is peeled off (`Vdir_Vword`), `Vdir` is applied to the presentation
(`Vdir_sum_mul`), and each `Vdir` of a term `eaEvalC c (opMono c h ι μ f)` is rewritten by the frame
identity `Vdir_eaEvalC` and the prepend identity `detOp_opMono_prepend`. -/
theorem pres_Vword (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (f : EAPoly k r) (a : Fin k → ℂ) (hd : jacValC c h ι a ≠ 0) (ν : Fin k → ℕ)
    (hν : ∀ b, ν (ι b) = 0) :
    Pres c h ι f a ν (Vword c h ι ν (fun z => Work.WilE3.eaEvalC c f z)) := by
  classical
  have key : ∀ N : ℕ, ∀ ν : Fin k → ℕ, (∀ b, ν (ι b) = 0) → (∑ l, ν l) ≤ N →
      Pres c h ι f a ν (Vword c h ι ν (fun z => Work.WilE3.eaEvalC c f z)) := by
    intro N
    induction N with
    | zero =>
      intro ν hν hsum
      have hν0 : ν = 0 := funext fun i => Nat.eq_zero_of_le_zero (le_trans
        (Finset.single_le_sum (fun j _ => Nat.zero_le (ν j)) (Finset.mem_univ i)) hsum)
      subst hν0
      exact pres_zero c h ι f a
    | succ N ih =>
      intro ν hν hsum
      by_cases hz0 : ν = 0
      · subst hz0
        exact pres_zero c h ι f a
      · obtain ⟨l, hl_ne, hl0⟩ : ∃ l : Fin k, ν l ≠ 0 ∧ ∀ i : Fin k, i < l → ν i = 0 := by
          have hne : (Finset.univ.filter (fun i : Fin k => ν i ≠ 0)).Nonempty := by
            obtain ⟨i, hi⟩ := Function.ne_iff.mp hz0
            exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, by simpa using hi⟩⟩
          refine ⟨(Finset.univ.filter (fun i : Fin k => ν i ≠ 0)).min' hne,
            (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2, fun i hi => ?_⟩
          by_contra hcon
          have hmem : i ∈ Finset.univ.filter (fun i : Fin k => ν i ≠ 0) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ i, hcon⟩
          exact absurd hi (not_lt.mpr (Finset.min'_le _ i hmem))
        have hl_rng : l ∉ Set.range ι := by
          rintro ⟨b, hb⟩
          exact hl_ne (hb ▸ hν b)
        set ν' : Fin k → ℕ := Function.update ν l (ν l - 1) with hν'def
        have hν'l : ν' l = ν l - 1 := by rw [hν'def, Function.update_self]
        have hν'supp : ∀ b, ν' (ι b) = 0 := by
          intro b
          rw [hν'def, Function.update_of_ne (fun hh : ι b = l => hl_rng ⟨b, hh⟩) (ν l - 1) ν]
          exact hν b
        have hν'le : ∀ m, ν' m ≤ ν m := by
          intro m
          by_cases hm : m = l
          · subst hm
            rw [hν'l]
            exact Nat.sub_le _ _
          · rw [hν'def, Function.update_of_ne hm (ν l - 1) ν]
        have hm' : ∀ i : Fin k, i < l → ν' i = 0 := fun i hi => by
          rw [hν'def, Function.update_of_ne (ne_of_lt hi) (ν l - 1) ν]
          exact hl0 i hi
        have hlt : ∑ i, ν' i < ∑ i, ν i := by
          refine Finset.sum_lt_sum (fun i _ => hν'le i) ⟨l, Finset.mem_univ l, ?_⟩
          rw [hν'l]
          exact Nat.sub_lt (Nat.pos_of_ne_zero hl_ne) Nat.one_pos
        have hbound : ∑ i, ν' i ≤ N := by omega
        obtain ⟨K, g, μ, hcond, hgan, hF⟩ := ih ν' hν'supp hbound
        have hpeel : Vword c h ι ν (fun z => Work.WilE3.eaEvalC c f z)
            = Vdir c h ι l (Vword c h ι ν' (fun z => Work.WilE3.eaEvalC c f z)) := by
          have hupd : Function.update ν' l (ν' l + 1) = ν := by
            funext i
            by_cases hi : i = l
            · subst hi
              rw [Function.update_self, hν'l]
              exact Nat.sub_add_cancel (Nat.pos_of_ne_zero hl_ne)
            · rw [Function.update_of_ne hi (ν' l + 1) ν', hν'def,
                Function.update_of_ne hi (ν l - 1) ν]
          have hV := Vdir_Vword c h ι l ν' hm' (fun z => Work.WilE3.eaEvalC c f z)
          rw [hupd] at hV
          exact hV.symm
        set E : Fin K → (Fin k → ℂ) → ℂ :=
          fun i => fun z => Work.WilE3.eaEvalC c (opMono c h ι (μ i) f) z with hEdef
        set E' : Fin K → (Fin k → ℂ) → ℂ :=
          fun i => fun z =>
            Work.WilE3.eaEvalC c (opMono c h ι (Function.update (μ i) l (μ i l + 1)) f) z
          with hE'def
        have hEan : ∀ i, AnalyticAt ℂ (E i) a := by
          intro i
          rw [hEdef]
          exact (Work.WilE3.API.eaEvalC_fderiv_analytic c (opMono c h ι (μ i) f) a).1
        have hΔev : ∀ᶠ z in 𝓝 a, jacValC c h ι z ≠ 0 := eventually_jacValC_ne_zero c h ι hd
        have hVdirE : ∀ i : Fin K, Vdir c h ι l (E i) =ᶠ[𝓝 a]
            fun z => (jacValC c h ι z)⁻¹ * E' i z := by
          intro i
          filter_upwards [hΔev] with z hz
          have hμ0 : ∀ m : Fin k, m < l → μ i m = 0 := by
            intro m hm
            have h1 : μ i m ≤ ν' m := (hcond i).2 m
            rw [hm' m hm] at h1
            exact Nat.eq_zero_of_le_zero h1
          rw [Vdir_eaEvalC c h ι l hz (opMono c h ι (μ i) f)]
          rw [detOp_opMono_prepend c h ι l (μ i) hμ0 f]
        have hstep2 : Vdir c h ι l (Vword c h ι ν' (fun z => Work.WilE3.eaEvalC c f z))
            =ᶠ[𝓝 a] Vdir c h ι l (fun z => ∑ i, g i z * E i z) := Vdir_congr c h ι l hF
        have hstep3 := Vdir_sum_mul' c h ι l K g E a hgan hEan
        have hstep4 : (fun z => ∑ i, (Vdir c h ι l (g i) z * E i z
              + g i z * Vdir c h ι l (E i) z))
            =ᶠ[𝓝 a] (fun z => ∑ i, (Vdir c h ι l (g i) z * E i z
              + g i z * ((jacValC c h ι z)⁻¹ * E' i z))) := by
          refine eventuallyEq_sum_univ (fun i => ?_)
          have h1 : (fun z => g i z * Vdir c h ι l (E i) z)
              =ᶠ[𝓝 a] (fun z => g i z * ((jacValC c h ι z)⁻¹ * E' i z)) :=
            (Filter.EventuallyEq.refl (𝓝 a) (fun z => g i z)).mul (hVdirE i)
          exact (Filter.EventuallyEq.refl (𝓝 a) (fun z => Vdir c h ι l (g i) z * E i z)).add h1
        have hchain : Vword c h ι ν (fun z => Work.WilE3.eaEvalC c f z) =ᶠ[𝓝 a]
            (fun z => ∑ i, (Vdir c h ι l (g i) z * E i z
              + g i z * ((jacValC c h ι z)⁻¹ * E' i z))) := by
          rw [hpeel]
          exact hstep2.trans (hstep3.trans hstep4)
        set g' : Fin (K + K) → (Fin k → ℂ) → ℂ :=
          Fin.addCases (fun i => Vdir c h ι l (g i))
            (fun i => fun z => (jacValC c h ι z)⁻¹ * g i z) with hg'def
        set μ' : Fin (K + K) → Fin k → ℕ :=
          Fin.addCases (fun i => μ i) (fun i => Function.update (μ i) l (μ i l + 1)) with hμ'def
        have hcond' : ∀ j : Fin (K + K), (∀ b, μ' j (ι b) = 0) ∧ (∀ m, μ' j m ≤ ν m) := by
          intro j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · rw [show μ' (Fin.castAdd K i) = μ i from by simp only [hμ'def, Fin.addCases_left]]
            exact ⟨(hcond i).1, fun m => le_trans ((hcond i).2 m) (hν'le m)⟩
          · rw [show μ' (Fin.natAdd K i) = Function.update (μ i) l (μ i l + 1)
                from by simp only [hμ'def, Fin.addCases_right]]
            refine ⟨fun b => ?_, fun m => ?_⟩
            · rw [Function.update_of_ne (fun hh : ι b = l => hl_rng ⟨b, hh⟩) (μ i l + 1) (μ i)]
              exact (hcond i).1 b
            · by_cases hm : m = l
              · rw [hm, Function.update_self]
                have h1 : μ i l ≤ ν' l := (hcond i).2 l
                rw [hν'l] at h1
                omega
              · rw [Function.update_of_ne hm (μ i l + 1) (μ i)]
                exact le_trans ((hcond i).2 m) (hν'le m)
        have hgan' : ∀ j : Fin (K + K), AnalyticAt ℂ (g' j) a := by
          intro j
          refine Fin.addCases (fun i => ?_) (fun i => ?_) j
          · rw [show g' (Fin.castAdd K i) = Vdir c h ι l (g i)
                from by simp only [hg'def, Fin.addCases_left]]
            exact analyticAt_Vdir' c h ι l hd (hgan i)
          · rw [show g' (Fin.natAdd K i) = (fun z => (jacValC c h ι z)⁻¹ * g i z)
                from by simp only [hg'def, Fin.addCases_right]]
            exact (AnalyticAt.inv (analyticAt_jacValC c h ι a) hd).mul (hgan i)
        have hEfun : (fun z => ∑ j : Fin (K + K),
              g' j z * Work.WilE3.eaEvalC c (opMono c h ι (μ' j) f) z)
            = fun z => ∑ i, (Vdir c h ι l (g i) z * E i z
                + g i z * ((jacValC c h ι z)⁻¹ * E' i z)) := by
          funext z
          simp only [hEdef, hE'def]
          rw [hg'def, hμ'def, Fin.sum_univ_add]
          simp only [Fin.addCases_left, Fin.addCases_right]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        refine ⟨K + K, g', μ', hcond', hgan', ?_⟩
        exact hchain.trans (Filter.EventuallyEq.of_eq hEfun).symm
  exact key (∑ l, ν l) ν hν le_rfl

/-! ## §4. The target -/

/-- **The algebraic core of the frame step.**  If all the *ordered* reduced derivatives
`opMono c h ι m f` (of order `≤ M`) of `f` vanish at the real point `x`, then so does every iterated
derivative of `f` at `x` along the tangential frame `VcoefC` of `{h = 0}` — here expressed as the
`V`-word `Vword c h ι m` applied to the function `z ↦ eaEvalC c f z`, evaluated at `x`.

The proof is the triangularity `V_l = Δ⁻¹ (detOp l)` (`eaEvalC_detOp_eq`) together with the
prepend identities `Vdir_Vword`, `detOp_opMono_prepend`: by strong induction on the order, each
`V`-word is a `C^ω`-combination of the `opMono` words of no larger multi-index, and those vanish at
`x` by hypothesis. -/
theorem Vword_toC_eq_zero {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (f : EAPoly k r) (x : Fin k → ℝ) (M : ℕ)
    (hvan : ∀ m : Fin k → ℕ, (∀ a, m (ι a) = 0) → (∑ l, m l) ≤ M →
      eaEval c (opMono c h ι m f) x = 0)
    (hd : Work.WilE3.Frame.jacValC c h ι (Work.WilE3.Frame.toC x) ≠ 0)
    (m : Fin k → ℕ) (hm : ∀ a, m (ι a) = 0) (hM : ∑ l, m l ≤ M) :
    Work.WilE3.Frame.Vword c h ι m (fun z => Work.WilE3.eaEvalC c f z)
      (Work.WilE3.Frame.toC x) = 0 := by
  obtain ⟨K, g, μ, hcond, hgan, hF⟩ := pres_Vword c h ι f (toC x) hd m hm
  rw [hF.eq_of_nhds]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [eaEvalC_toC,
    hvan (μ i) (hcond i).1 (le_trans (Finset.sum_le_sum fun l _ => (hcond i).2 l) hM)]
  simp

end

end Work.WilE3.Frame
