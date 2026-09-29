import Mathlib
import Submission.Work.Resample.axKit
import Submission.Work.Resample.fxTensorErr
import Submission.Work.Resample.axisList_one_getD
import Submission.Work.Resample.axisFx1Gen_getD
import Submission.Work.Resample.axisList_blkAlt

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ### Basic facts -/

lemma prod_nil_pos : (0 : ℕ) < ([] : List ℕ).prod := by simp

lemma prod_pos_getD : ∀ (l : List ℕ), (∀ j < l.length, 0 < l.getD j 0) → 0 < l.prod
  | [], _ => by simp
  | a :: l, h => by
    rw [List.prod_cons]
    refine Nat.mul_pos (by simpa using h 0 (by simp)) (prod_pos_getD l (fun j hj => ?_))
    exact h (j+1) (by simp only [List.length_cons]; omega)

lemma blk_bound {A s B a jj K : ℕ} (ha : a < A) (hj : jj < s) (hK : K < B) :
    a * (s * B) + jj * B + K < A * (s * B) := by
  have h1 : jj * B + K < s * B := mul_add_lt_mul hj hK
  have h2 : a * (s * B) + (jj * B + K) < a * (s * B) + s * B := Nat.add_lt_add_left h1 _
  have h3 : a * (s * B) + s * B = (a + 1) * (s * B) := by ring
  have h4 : (a + 1) * (s * B) ≤ A * (s * B) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt ha)
  omega

lemma fxBlk_bound {A : ℕ} {ss ts : List ℕ} (h : 0 < ts.prod) (J : Fin (A * ts.prod))
    (i : Fin ss.prod) : (J : ℕ) / ts.prod * ss.prod + (i : ℕ) < A * ss.prod := by
  have hJ : (J : ℕ) / ts.prod < A := (Nat.div_lt_iff_lt_mul h).mpr J.isLt
  have h1 : (J : ℕ) / ts.prod * ss.prod + (i : ℕ)
      < ((J : ℕ) / ts.prod + 1) * ss.prod := by
    rw [Nat.add_mul]
    simpa using Nat.add_lt_add_left i.isLt ((J : ℕ) / ts.prod * ss.prod)
  have h2 : ((J : ℕ) / ts.prod + 1) * ss.prod ≤ A * ss.prod :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hJ)
  omega

lemma fxTensorRec_cons' {s t : ℕ} {ss' ts' : List ℕ}
    (Φ : (i : ℕ) → (Fin ((s :: ss').getD i 0) → ℤ × ℤ) → (Fin ((t :: ts').getD i 0) → ℤ × ℤ))
    (v : Fin ((s :: ss').prod) → ℤ × ℤ) :
    fxTensorRec (s :: ss') (t :: ts') Φ v
      = fxBlockwise t ss'.prod ts'.prod (fxTensorRec ss' ts' (famShift' Φ))
          (axisFx1Gen s t ss'.prod (Φ 0) v) := rfl

lemma fxBlk_apply_pos (A : ℕ) (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (u : Fin (A * ss.prod) → ℤ × ℤ) (h : 0 < ts.prod) (J : Fin (A * ts.prod)) :
    fxBlk A ss ts Φ u J = fxTensorRec ss ts Φ (fun i : Fin ss.prod =>
      u ⟨(J : ℕ) / ts.prod * ss.prod + (i : ℕ), fxBlk_bound h J i⟩)
        ⟨(J : ℕ) % ts.prod, Nat.mod_lt _ h⟩ := by
  unfold fxBlk
  rw [dif_pos h]

lemma axisIterA_one (A s t : ℕ) (ss' ts' : List ℕ)
    (Φ : (i : ℕ) → (Fin ((s::ss').getD i 0) → ℤ × ℤ) → (Fin ((t::ts').getD i 0) → ℤ × ℤ))
    (zs : List (ℤ × ℤ)) :
    axisIterA A (s::ss') (t::ts') Φ 1 zs = axisList (A * 1) s t ss'.prod (Φ 0) zs := rfl

/-! ### Locality of one axis pass -/

lemma axisList_step_getD {A s t B : ℕ} (Φ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ))
    (u : Fin (A * (s * B)) → ℤ × ℤ) (ht : 0 < t) (hB : 0 < B)
    (a : ℕ) (ha : a < A) (j : ℕ) (hj : j < t) (K : ℕ) (hK : K < B) :
    (axisList (A * 1) s t B Φ (List.ofFn u)).getD (a * (t * B) + j * B + K) (0,0)
      = Φ (fun jj : Fin s => u ⟨a * (s * B) + (jj : ℕ) * B + K, blk_bound ha jj.isLt hK⟩)
          ⟨j, hj⟩ := by
  have hA : A * 1 = 1 * A := by ring
  rw [hA]
  rw [axisList_blkAlt (X := 1) (t := A) (m := s) (n := t) (B := B) Φ (List.ofFn u) ht hB]
  rw [show 1 * s * B = s * B from by ring]
  have hlen : ∀ g < A, (axisList 1 s t B Φ (blk (s * B) g (List.ofFn u))).length = t * B := by
    intro g hg
    rw [axisList_length]
    ring
  rw [show a * (t * B) + j * B + K = a * (t * B) + (j * B + K) from by ring]
  rw [flatMap_getD A (t * B) (fun g => axisList 1 s t B Φ (blk (s * B) g (List.ofFn u)))
    hlen a (j * B + K) ha (mul_add_lt_mul hj hK)]
  rw [axisList_one_getD s t B Φ (blk (s * B) a (List.ofFn u)) ht hB j K hj hK]
  congr 1
  funext jj
  rw [blk_getD (s * B) a ((jj : ℕ) * B + K) (List.ofFn u) (mul_add_lt_mul jj.isLt hK)]
  rw [show a * (s * B) + ((jj : ℕ) * B + K) = a * (s * B) + (jj : ℕ) * B + K from by ring]
  rw [ofFn_getD u (blk_bound ha jj.isLt hK)]

/-! ### The blockwise recursion of `fxBlk` -/

lemma fxBlk_cons (A s t : ℕ) (ss' ts' : List ℕ)
    (Φ : (i : ℕ) → (Fin ((s :: ss').getD i 0) → ℤ × ℤ) → (Fin ((t :: ts').getD i 0) → ℤ × ℤ))
    (u : Fin (A * (s * ss'.prod)) → ℤ × ℤ) (F : ℕ → ℤ × ℤ)
    (hF : ∀ (a : ℕ) (ha : a < A) (j : ℕ) (hj : j < t) (K : ℕ) (hK : K < ss'.prod),
      F (a * (t * ss'.prod) + j * ss'.prod + K) = Φ 0 (fun jj : Fin s =>
        u ⟨a * (s * ss'.prod) + (jj : ℕ) * ss'.prod + K, blk_bound ha jj.isLt hK⟩) ⟨j, hj⟩)
    (ht : 0 < t) (hts : 0 < ts'.prod) (hss : 0 < ss'.prod)
    (J : ℕ) (hJ : J < A * (t * ts'.prod)) (hJ' : J < (A * t) * ts'.prod) :
    fxBlk A (s :: ss') (t :: ts') Φ u ⟨J, hJ⟩
      = fxBlk (A * t) ss' ts' (famShift' Φ) (fun i : Fin ((A * t) * ss'.prod) => F (i : ℕ))
          ⟨J, hJ'⟩ := by
  have hprops : 0 < (t :: ts').prod := Nat.mul_pos ht hts
  rw [fxBlk_apply_pos A (s :: ss') (t :: ts') Φ u hprops ⟨J, hJ⟩]
  rw [fxBlk_apply_pos (A * t) ss' ts' (famShift' Φ) (fun i : Fin ((A * t) * ss'.prod) => F (i : ℕ))
    hts ⟨J, hJ'⟩]
  simp only [List.prod_cons]
  rw [fxTensorRec_cons' Φ (fun i : Fin (s * ss'.prod) =>
    u ⟨J / (t * ts'.prod) * (s * ss'.prod) + (i : ℕ),
      fxBlk_bound (ss := s :: ss') (ts := t :: ts') hprops ⟨J, hJ⟩ i⟩)]
  rw [fxTE_fxBlockwise_apply hts]
  have hmod : J % (t * ts'.prod) % ts'.prod = J % ts'.prod := by
    rw [Nat.mul_comm t ts'.prod, Nat.mod_mul_right_mod]
  have hdiv : J % (t * ts'.prod) / ts'.prod = J / ts'.prod % t := by
    rw [Nat.mul_comm t ts'.prod, Nat.mod_mul_right_div_self]
  have hq : J / (t * ts'.prod) * t + J / ts'.prod % t = J / ts'.prod := by
    have h1 : J / (t * ts'.prod) = J / ts'.prod / t := by
      rw [Nat.mul_comm t ts'.prod, Nat.div_div_eq_div_mul]
    rw [h1, Nat.mul_comm (J / ts'.prod / t) t]
    exact Nat.div_add_mod (J / ts'.prod) t
  have hvec : (fun K' : Fin ss'.prod => zget (axisFx1Gen s t ss'.prod (Φ 0)
        (fun i : Fin (s * ss'.prod) =>
          u ⟨J / (t * ts'.prod) * (s * ss'.prod) + (i : ℕ),
            fxBlk_bound (ss := s :: ss') (ts := t :: ts') hprops ⟨J, hJ⟩ i⟩))
        (J % (t * ts'.prod) / ts'.prod * ss'.prod + (K' : ℕ)))
      = (fun i : Fin ss'.prod => F (J / ts'.prod * ss'.prod + (i : ℕ))) := by
    funext K'
    rw [hdiv]
    rw [fxTE_zget_of_lt _ (mul_add_lt_mul (Nat.mod_lt _ ht) K'.isLt)]
    rw [axisFx1Gen_getD s t ss'.prod (Φ 0) (fun i : Fin (s * ss'.prod) =>
      u ⟨J / (t * ts'.prod) * (s * ss'.prod) + (i : ℕ),
        fxBlk_bound (ss := s :: ss') (ts := t :: ts') hprops ⟨J, hJ⟩ i⟩)
      ht hss (J / ts'.prod % t) (K' : ℕ) (Nat.mod_lt _ ht) K'.isLt]
    have hidx : J / (t * ts'.prod) * (t * ss'.prod) + (J / ts'.prod % t) * ss'.prod + (K' : ℕ)
        = J / ts'.prod * ss'.prod + (K' : ℕ) := by
      calc J / (t * ts'.prod) * (t * ss'.prod) + (J / ts'.prod % t) * ss'.prod + (K' : ℕ)
          = (J / (t * ts'.prod) * t + J / ts'.prod % t) * ss'.prod + (K' : ℕ) := by ring
        _ = J / ts'.prod * ss'.prod + (K' : ℕ) := by rw [hq]
    rw [← hidx]
    rw [hF (J / (t * ts'.prod)) ((Nat.div_lt_iff_lt_mul hprops).mpr hJ) (J / ts'.prod % t)
      (Nat.mod_lt _ ht) (K' : ℕ) K'.isLt]
    apply congrArg (fun g : Fin t → ℤ × ℤ => g ⟨J / ts'.prod % t, Nat.mod_lt _ ht⟩)
    apply congrArg (Φ 0)
    funext jj
    apply congrArg u
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  rw [hvec]
  apply congrArg (fxTensorRec ss' ts' (famShift' Φ)
    (fun i : Fin ss'.prod => F (J / ts'.prod * ss'.prod + (i : ℕ))))
  apply Fin.ext
  simp only [Fin.val_mk, hmod]

/-! ### The main induction -/

theorem axisIterA_ofFn (ss : List ℕ) :
    ∀ (ts : List ℕ), ts.length = ss.length →
    (∀ j < ss.length, 0 < ss.getD j 0) → (∀ j < ss.length, 0 < ts.getD j 0) →
    ∀ (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
      (A : ℕ) (u : Fin (A * ss.prod) → ℤ × ℤ),
      axisIterA A ss ts Φ ss.length (List.ofFn u) = List.ofFn (fxBlk A ss ts Φ u) := by
  induction ss with
  | nil =>
    intro ts hl hpos hpos' Φ A u
    have hts : ts = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst hts
    rw [List.length_nil, axisIterA_zero]
    apply List.ofFn_inj.mpr
    funext J
    rw [fxBlk_apply_pos A [] [] Φ u prod_nil_pos J]
    have hfun : (fun i : Fin ([] : List ℕ).prod =>
        u ⟨(J : ℕ) / ([] : List ℕ).prod * ([] : List ℕ).prod + (i : ℕ),
          fxBlk_bound (ss := []) (ts := []) prod_nil_pos J i⟩)
        = (fun _ : Fin ([] : List ℕ).prod => u J) := by
      funext i
      have h1 : (i : ℕ) = 0 := by
        have := i.isLt
        simp only [List.prod_nil] at this
        omega
      have h2 : (⟨(J : ℕ) / ([] : List ℕ).prod * ([] : List ℕ).prod + (i : ℕ),
          fxBlk_bound (ss := []) (ts := []) prod_nil_pos J i⟩ : Fin (A * ([] : List ℕ).prod)) = J := by
        apply Fin.ext
        simp only [Fin.val_mk, List.prod_nil, Nat.div_one, Nat.mul_one, h1, Nat.add_zero]
      rw [h2]
    rw [hfun]
    rfl
  | cons s ss' ih =>
    intro ts hl hpos hpos' Φ A u
    cases ts with
    | nil => simp at hl
    | cons t ts' =>
      have hTS : ts'.length = ss'.length := by simpa using hl
      have hposT : ∀ j < ss'.length, 0 < ss'.getD j 0 :=
        fun j hj => hpos (j+1) (by simp only [List.length_cons]; omega)
      have hposT' : ∀ j < ts'.length, 0 < ts'.getD j 0 :=
        fun j hj => hpos' (j+1) (by simp only [List.length_cons]; omega)
      have ht : 0 < t := hpos' 0 (by simp)
      have hssP : 0 < ss'.prod := prod_pos_getD ss' hposT
      have htsP : 0 < ts'.prod := prod_pos_getD ts' hposT'
      rw [show (s :: ss').length = ss'.length + 1 from rfl,
        axisIterA_tail A s t ss' ts' Φ ss'.length (List.ofFn u)]
      rw [axisIterA_one A s t ss' ts' Φ (List.ofFn u)]
      set Ψ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ) := Φ 0 with hΨ
      have hF1len : (axisList (A * 1) s t ss'.prod Ψ (List.ofFn u)).length = (A * t) * ss'.prod := by
        rw [axisList_length]; ring
      rw [← ofFn_getD_of_length (axisList (A * 1) s t ss'.prod Ψ (List.ofFn u))
        ((A * t) * ss'.prod) hF1len]
      rw [ih ts' hTS hposT (fun j hj => hposT' j (by rw [hTS]; exact hj)) (famShift' Φ) (A * t)
        (fun i : Fin ((A * t) * ss'.prod) =>
          (axisList (A * 1) s t ss'.prod Ψ (List.ofFn u)).getD (i : ℕ) (0,0))]
      refine ofFn_eq_of_assoc (N := (A * t) * ts'.prod) (M := A * (t * ts'.prod))
        (Nat.mul_assoc A t ts'.prod)
        (fun i hN => fxBlk (A * t) ss' ts' (famShift' Φ)
          (fun i : Fin ((A * t) * ss'.prod) =>
            (axisList (A * 1) s t ss'.prod Ψ (List.ofFn u)).getD (i : ℕ) (0,0)) ⟨i, hN⟩)
        (fun i hM => fxBlk A (s :: ss') (t :: ts') Φ u ⟨i, hM⟩) ?_
      intro i hN hM
      exact (fxBlk_cons A s t ss' ts' Φ u
        (fun i => (axisList (A * 1) s t ss'.prod Ψ (List.ofFn u)).getD i (0,0))
        (fun a ha j hj K hK => axisList_step_getD Ψ u ht hssP a ha j hj K hK)
        ht htsP hssP i hM hN).symm

/-! ### The final statement -/

lemma fxBlk_one_apply (ss ts : List ℕ)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (u : Fin (1 * ss.prod) → ℤ × ℤ) (h : 0 < ts.prod) (v : Fin ss.prod → ℤ × ℤ)
    (hv : ∀ i : Fin ss.prod, u ⟨(i : ℕ), by rw [Nat.one_mul]; exact i.isLt⟩ = v i)
    (J : ℕ) (hJ : J < ts.prod) :
    fxBlk 1 ss ts Φ u ⟨J, by rw [Nat.one_mul]; exact hJ⟩ = fxTensorRec ss ts Φ v ⟨J, hJ⟩ := by
  rw [fxBlk_apply_pos 1 ss ts Φ u h ⟨J, by rw [Nat.one_mul]; exact hJ⟩]
  congr 1
  · funext i
    have hfin : (⟨(J : ℕ) / ts.prod * ss.prod + (i : ℕ),
        fxBlk_bound h ⟨J, by rw [Nat.one_mul]; exact hJ⟩ i⟩ : Fin (1 * ss.prod))
        = ⟨(i : ℕ), by rw [Nat.one_mul]; exact i.isLt⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk, Nat.div_eq_of_lt hJ, Nat.zero_mul, Nat.zero_add]
    rw [hfin]
    exact hv i
  · apply Fin.ext
    simp only [Fin.val_mk, Nat.mod_eq_of_lt hJ]

theorem axisIter_getD_fxTensorRec (ss ts : List ℕ) (hl : ts.length = ss.length)
    (hpos : ∀ j < ss.length, 0 < ss.getD j 0) (hpos' : ∀ j < ss.length, 0 < ts.getD j 0)
    (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (es : List (ℤ × ℤ)) (hlen : es.length = ss.prod) (J : ℕ) (hJ : J < ts.prod) :
    (Work.Resample.axisIter ss ts Φ ss.length es).getD J (0, 0) =
      Work.Resample.fxTensorRec ss ts Φ (fun i : Fin ss.prod => es.getD i (0, 0)) ⟨J, hJ⟩ := by
  have htsP : 0 < ts.prod := prod_pos_getD ts (fun j hj => hpos' j (by rwa [hl] at hj))
  have h1ss : List.ofFn (fun i : Fin (1 * ss.prod) => es.getD (i : ℕ) (0,0)) = es :=
    (ofFn_eq_of_assoc (N := 1 * ss.prod) (M := ss.prod) (Nat.one_mul ss.prod)
      (fun i _ => es.getD i (0,0)) (fun i _ => es.getD i (0,0)) (fun i _ _ => rfl)).trans
      (ofFn_getD_of_length es ss.prod hlen)
  have hstep : axisIter ss ts Φ ss.length es
      = List.ofFn (fxBlk 1 ss ts Φ (fun i : Fin (1 * ss.prod) => es.getD (i : ℕ) (0,0))) := by
    rw [axisIter_eq_axisIterA_one]
    conv_lhs => rw [← h1ss]
    exact axisIterA_ofFn ss ts hl hpos hpos' Φ 1 _
  rw [hstep, ofFn_getD (fxBlk 1 ss ts Φ
    (fun i : Fin (1 * ss.prod) => es.getD (i : ℕ) (0,0))) (by rw [Nat.one_mul]; exact hJ)]
  exact fxBlk_one_apply ss ts Φ _ htsP (fun i : Fin ss.prod => es.getD (i : ℕ) (0,0))
    (fun i => rfl) J hJ

end Work.Resample
