import Mathlib
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.jet_comp_l2
import Submission.Work.Diff.STE.flat.inv_jet_bound
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.continuous_pdVec
import Submission.Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.STE.flat.jetP_iteratedFDeriv_bound`

The `L²` and sup bounds for the iterated Fréchet derivatives of the value-and-first-jet map

  `jetP c x = (seriesFunM c x, fun a i j => ∂_a (seriesFunM c · i j) x)`

of a coefficient family `c` supported in `box n N` whose level-`s` energy satisfies
`ENormSqFull s (seriesFunM c) ≤ Bs²`:

* `∫_{cube} ‖D^m (jetP c) x‖² ≤ C (1 + Bs² + ENormSqM (s+1) + ENormSqM (s+2))` for `m ≤ s+1`;
* `‖D^m (jetP c) x‖ ≤ C (1 + Bs)` for `m ≤ M` with `M + 1 + sob n ≤ s`.

## Route

Everything is reduced, componentwise, to a *single entry* `d_{ij} = seriesFunM c · i j`, which is
the Fourier series `seriesFun (fun k => c k i j)`.

* **The operator norm versus the partial derivatives.**  Expanding an `m`-multilinear map on
  `(Fin n → ℝ)^m` in the standard basis gives `‖T‖ ≤ Σ_{l} ‖T (basis l)‖`
  (`norm_le_sum_basis_tuple`); with `pdVec_eq_iteratedFDeriv` this bounds `‖D^m f x‖` by
  `Σ_l ‖pdVec m l f x‖` (`norm_iteratedFDeriv_le_sum_pdVec`) and, after Cauchy–Schwarz on the
  cube (`JetComp.integral_sq_sum_le`), integrates to
  `∫ ‖D^m f x‖² ≤ n^m · ENormSq m f` (`int_iteratedFDeriv_sq_le_ENormSq_aux`, the same statement as
  the delegated `Work.Diff.STE.flat.integral_iteratedFDeriv_sq_le_ENormSq`).
* **The entrywise energy.**  `∫ ‖∂^p (seriesFun d)‖² ≤ ((2π)²)^p · CSq p d`
  (`invJet_integral_pdVec_seriesFun_le`), `CSq` is monotone in the level (`invJet_CSq_mono_le`) and
  `CSq k (entry) ≤ C · ENormSqFull k (seriesFunM c)` uniformly (`invJet_CSq_entry_le_uniform`);
  this gives `ENormSq p (entry) ≤ C · ENormSqFull (s+2) (seriesFunM c)` for all `p ≤ s+2`
  (`ENormSq_entry_le`).  For the first coordinate derivative one uses
  `pdVec m l (∂_a u) = pdVec (m+1) (Fin.append l ![a]) u` (`pdVec_pd_eq`), hence
  `ENormSq m (∂_a u) ≤ n^m · ENormSq (m+1) u` (`ENormSq_pd_le`).
* **The sup bound** is the Sobolev embedding `‖seriesFun c x‖ ≤ C0 √(CSq (sob n) c)`
  (`norm_seriesFun_le`) combined with the same entrywise comparison (`pdVec_entry_sup_le`).
* **Assembly.**  The jet of a pair is the pair of the jets (`iteratedFDeriv_prodMk`), the norm of a
  pair is the maximum of the norms, and the jet of a tuple is at most the sum of the jets of its
  components (`Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum`); this bounds `‖D^m (jetP c) x‖` by the
  sum of the component jets (`norm_iteratedFDeriv_jetP_le`).  Cauchy–Schwarz over the (finitely
  many) components and the entrywise bounds then give the claim.
-/

namespace Work.Diff.STE.flat

set_option maxHeartbeats 2000000

open MeasureTheory BigOperators
open Work.Diff.STE.Flat

noncomputable section

lemma contDiff_pd_top_jetP {n : ℕ} {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd j f) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : Fin n → ℝ => (Pi.single j (1 : ℝ) : Fin n → ℝ)) := contDiff_const
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin n → ℝ => (fderiv ℝ f x) (Pi.single j (1 : ℝ))) := h1.clm_apply hc
  exact h2

lemma contDiff_entry_seriesFunM {n : ℕ} (N : ℕ) (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => seriesFunM c y i j) := by
  have h : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = Work.Diff.STE.seriesFun (fun k => c k i j) := by
    funext y; rw [seriesFunM_apply]
  rw [h]
  exact Work.Diff.STE.contDiff_seriesFun _ (fun M => summable_moment_box c hc i j M)

lemma contDiff_pd_entry_seriesFunM {n : ℕ} (N : ℕ) (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) (a i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) :=
  contDiff_pd_top_jetP (contDiff_entry_seriesFunM N c hc i j) a

lemma contDiff_seriesFunM_mat {n : ℕ} (N : ℕ) (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => seriesFunM c y) :=
  contDiff_pi' (fun i => contDiff_pi' (fun j => contDiff_entry_seriesFunM N c hc i j))

lemma contDiff_snd_jetP {n : ℕ} (N : ℕ) (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Fin n → ℝ => fun a i j => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) :=
  contDiff_pi' (fun a => contDiff_pi' (fun i => contDiff_pi'
    (fun j => contDiff_pd_entry_seriesFunM N c hc a i j)))

lemma contDiff_jetP {n : ℕ} (N : ℕ) (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (jetP c) :=
  ContDiff.prodMk (contDiff_seriesFunM_mat N c hc) (contDiff_snd_jetP N c hc)

lemma norm_iteratedFDeriv_jetP_le {n : ℕ} (N : ℕ) (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) (m : ℕ) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ m (jetP c) x‖
      ≤ (∑ i : Fin n, ∑ j : Fin n,
            ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y i j) x‖)
        + ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n,
            ‖iteratedFDeriv ℝ m
              (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖ := by
  have hmat : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => seriesFunM c y) :=
    contDiff_seriesFunM_mat N c hc
  have hvec : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ =>
      fun a i j => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) := contDiff_snd_jetP N c hc
  have hpair := iteratedFDeriv_prodMk (f := fun y : Fin n → ℝ => seriesFunM c y)
    (g := fun y : Fin n → ℝ => fun a i j => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y)
    (hmat.contDiffAt (x := x)) (hvec.contDiffAt (x := x)) (i := m)
    (WithTop.coe_le_coe.mpr le_top)
  have hjet : iteratedFDeriv ℝ m (jetP c) x
      = (iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y) x).prod
        (iteratedFDeriv ℝ m (fun y : Fin n → ℝ =>
          fun a i j => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x) := hpair
  rw [hjet, ContinuousMultilinearMap.opNorm_prod]
  have h1 : ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y) x‖
      ≤ ∑ i : Fin n, ∑ j : Fin n,
          ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ := by
    refine (Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum
      (fun y : Fin n → ℝ => seriesFunM c y) x m (hmat.contDiffAt (x := x))).trans ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hrow : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => seriesFunM c y i) :=
      contDiff_pi' (fun j => contDiff_entry_seriesFunM N c hc i j)
    exact Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum (fun y : Fin n → ℝ => seriesFunM c y i)
      x m (hrow.contDiffAt (x := x))
  have h2 : ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ =>
        fun a i j => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖
      ≤ ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          ‖iteratedFDeriv ℝ m
            (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖ := by
    refine (Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum
      (fun y : Fin n → ℝ =>
        fun a i j => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x m
      (hvec.contDiffAt (x := x))).trans ?_
    refine Finset.sum_le_sum (fun a _ => ?_)
    have ha : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ =>
        fun i j => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) :=
      contDiff_pi' (fun i => contDiff_pi'
        (fun j => contDiff_pd_entry_seriesFunM N c hc a i j))
    refine (Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum
      (fun y : Fin n → ℝ =>
        fun i j => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x m
      (ha.contDiffAt (x := x))).trans ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hai : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ =>
        fun j => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) :=
      contDiff_pi' (fun j => contDiff_pd_entry_seriesFunM N c hc a i j)
    exact Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum
      (fun y : Fin n → ℝ => fun j => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y)
      x m (hai.contDiffAt (x := x))
  have hsum1 : (0 : ℝ) ≤ ∑ i : Fin n, ∑ j : Fin n,
      ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
  have hsum2 : (0 : ℝ) ≤ ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n,
      ‖iteratedFDeriv ℝ m
        (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖ :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => norm_nonneg _)))
  exact max_le (h1.trans (le_add_of_nonneg_right hsum2)) (h2.trans (le_add_of_nonneg_left hsum1))

/-- `pdVec m l (∂_a u) = pdVec (m+1) (Fin.append l ![a]) u`.  Kept `private`: the same name is
declared in `flat/pairing_rest_le.lean`, and both modules are imported together downstream. -/
private lemma pdVec_pd_eq {n : ℕ} (m : ℕ) (l : Fin m → Fin n) (a : Fin n)
    (u : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pdVec (m + 1) (Fin.append l ![a]) u = Work.Diff.STE.pdVec m l (Work.Diff.STE.pd a u) := by
  simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_fin_append, List.foldr_append]
  rfl

/-- The `L²` norm of an `m`-fold derivative of `∂_a u` is controlled by the `H^{m+1}` energy. -/
lemma int_pdVec_pd_le_ENormSq_succ {n : ℕ} (m : ℕ) (a : Fin n) (u : (Fin n → ℝ) → ℂ)
    (l : Fin m → Fin n) :
    ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdVec m l (Work.Diff.STE.pd a u) x‖ ^ 2
      ≤ Work.Diff.STE.ENormSq (m + 1) u := by
  rw [← pdVec_pd_eq m l a u]
  exact int_pdVec_le_ENormSq u _

/-- The `H^m` energy of `∂_a u` is controlled by the `H^{m+1}` energy of `u`. -/
lemma ENormSq_pd_le {n : ℕ} (m : ℕ) (a : Fin n) (u : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.ENormSq m (Work.Diff.STE.pd a u)
      ≤ (Fintype.card (Fin m → Fin n) : ℝ) * Work.Diff.STE.ENormSq (m + 1) u := by
  have h1 : Work.Diff.STE.ENormSq m (Work.Diff.STE.pd a u)
      ≤ ∑ _l : Fin m → Fin n, Work.Diff.STE.ENormSq (m + 1) u := by
    rw [Work.Diff.STE.ENormSq]
    exact Finset.sum_le_sum (fun l _ => int_pdVec_pd_le_ENormSq_succ m a u l)
  calc Work.Diff.STE.ENormSq m (Work.Diff.STE.pd a u)
      ≤ ∑ _l : Fin m → Fin n, Work.Diff.STE.ENormSq (m + 1) u := h1
    _ = (Fintype.card (Fin m → Fin n) : ℝ) * Work.Diff.STE.ENormSq (m + 1) u := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]


/-- **A continuous multilinear map on `(Fin n → ℝ)^m` is bounded by the sum of its values on the
basis tuples.**  Expanding each argument in the standard basis (`Pi.single · 1`) and using
`‖v j (l j)‖ ≤ ‖v j‖` gives `‖T‖ ≤ (Σ_l ‖T (basis l)‖) * ∏ j ‖v j‖`. -/
lemma norm_le_sum_basis_tuple {n m : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin m => (Fin n → ℝ)) ℂ) :
    ‖T‖ ≤ ∑ l : Fin m → Fin n, ‖T (fun j => Pi.single (l j) (1 : ℝ))‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (f := T)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) (fun v => ?_)
  have hv : v = fun j => ∑ i : Fin n, (v j i) • Pi.single i (1 : ℝ) := by
    funext j
    refine (Finset.univ_sum_single (v j)).symm.trans ?_
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  conv_lhs => rw [hv]
  rw [ContinuousMultilinearMap.map_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ r : Fin m → Fin n,
      ‖T (fun j => (v j (r j)) • Pi.single (r j) (1 : ℝ))‖
        ≤ (∏ j, ‖v j‖) * ‖T (fun j => Pi.single (r j) (1 : ℝ))‖ := by
    intro r
    rw [ContinuousMultilinearMap.map_smul_univ, norm_smul, Real.norm_eq_abs, Finset.abs_prod]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    gcongr with j _
    exact norm_le_pi_norm (v j) (r j)
  calc ∑ r : Fin m → Fin n, ‖T (fun j => (v j (r j)) • Pi.single (r j) (1 : ℝ))‖
      ≤ ∑ r : Fin m → Fin n, (∏ j, ‖v j‖) * ‖T (fun j => Pi.single (r j) (1 : ℝ))‖ :=
        Finset.sum_le_sum (fun r _ => hterm r)
    _ = (∏ j, ‖v j‖)
          * ∑ r : Fin m → Fin n, ‖T (fun j => Pi.single (r j) (1 : ℝ))‖ := by
        rw [Finset.mul_sum]
    _ = (∑ r : Fin m → Fin n, ‖T (fun j => Pi.single (r j) (1 : ℝ))‖) * ∏ j, ‖v j‖ := by
        ring

/-- **The operator norm of the `m`-th derivative is bounded by the sum of the `L²`-type partial
derivatives.** -/
lemma norm_iteratedFDeriv_le_sum_pdVec {n : ℕ} (m : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ m f x‖
      ≤ ∑ l : Fin m → Fin n, ‖Work.Diff.STE.pdVec m l f x‖ := by
  refine (norm_le_sum_basis_tuple (iteratedFDeriv ℝ m f x)).trans ?_
  refine Finset.sum_le_sum (fun l _ => ?_)
  rw [← Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m f hf x l]

/-- **The `L²` bound for the `m`-th derivative of a smooth scalar function.** -/
lemma int_iteratedFDeriv_sq_le_ENormSq_aux {n : ℕ} (m : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖iteratedFDeriv ℝ m f x‖ ^ 2
      ≤ (Fintype.card (Fin m → Fin n) : ℝ) * Work.Diff.STE.ENormSq m f := by
  have hpdcont : ∀ l : Fin m → Fin n, Continuous (fun x : Fin n → ℝ =>
      ‖Work.Diff.STE.pdVec m l f x‖) := fun l =>
    (Work.Diff.STE.continuous_pdVec m l f (hf.of_le (WithTop.coe_le_coe.mpr le_top))).norm
  have hcont1 : Continuous (fun x : Fin n → ℝ => ‖iteratedFDeriv ℝ m f x‖ ^ 2) :=
    ((hf.continuous_iteratedFDeriv (by simp)).norm).pow 2
  have hcont2 : Continuous (fun x : Fin n → ℝ =>
      (∑ l : Fin m → Fin n, ‖Work.Diff.STE.pdVec m l f x‖) ^ 2) :=
    (continuous_finsetSum _ (fun l _ => hpdcont l)).pow 2
  have hmain : ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖iteratedFDeriv ℝ m f x‖ ^ 2
      ≤ ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          (∑ l : Fin m → Fin n, ‖Work.Diff.STE.pdVec m l f x‖) ^ 2 := by
    refine MeasureTheory.setIntegral_mono_on (JetComp.integrableOn_unitCube_of_continuous hcont1)
      (JetComp.integrableOn_unitCube_of_continuous hcont2) (JetComp.measSet_unitCube n) ?_
    intro x _
    have h := norm_iteratedFDeriv_le_sum_pdVec m f hf x
    have hnn : 0 ≤ ∑ l : Fin m → Fin n, ‖Work.Diff.STE.pdVec m l f x‖ :=
      Finset.sum_nonneg (fun l _ => norm_nonneg _)
    nlinarith [h, norm_nonneg (iteratedFDeriv ℝ m f x)]
  refine hmain.trans ?_
  have hcs := JetComp.integral_sq_sum_le
    (a := fun l : Fin m → Fin n => fun x => ‖Work.Diff.STE.pdVec m l f x‖)
    (fun l => hpdcont l) (fun l x => norm_nonneg _)
  rw [Work.Diff.STE.ENormSq]
  exact hcs



/-! ## Entrywise energy and sup bounds -/

/-- **The `L²` bound for one partial derivative of an entry of `seriesFunM c`.** -/
lemma int_pdVec_entry_le {n : ℕ} (k p : ℕ) (hp : p ≤ k) {Ck : ℝ} (hCk : 0 ≤ Ck)
    (hCk' : ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ κ : Fin n → ℤ, κ ∉ box n N → c κ = 0) → ∀ i j : Fin n,
      Work.Diff.STE.CSq k (fun m => c m i j) ≤ Ck * ENormSqFull k (seriesFunM c))
    {N : ℕ} {c : (Fin n → ℤ) → MatC n} (hc : ∀ κ : Fin n → ℤ, κ ∉ box n N → c κ = 0)
    (i j : Fin n) (l : Fin p → Fin n) :
    ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdVec p l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ ^ 2
      ≤ ((2 * Real.pi) ^ 2) ^ k * Ck * ENormSqFull k (seriesFunM c) := by
  have hmom : ∀ M : ℕ, Summable (fun κ : Fin n → ℤ => (Work.Diff.STE.wt κ) ^ M * ‖c κ i j‖) :=
    fun M => summable_moment_box c hc i j M
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = Work.Diff.STE.seriesFun (fun κ => c κ i j) := by
    funext y; rw [seriesFunM_apply]
  rw [hfun]
  refine (invJet_integral_pdVec_seriesFun_le (fun κ => c κ i j) hmom p l).trans ?_
  have hmono : Work.Diff.STE.CSq p (fun κ => c κ i j) ≤ Work.Diff.STE.CSq k (fun κ => c κ i j) :=
    invJet_CSq_mono_le _ hp (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ hmom k)
  have h2 := hCk' N c hc i j
  have hpow : ((2 * Real.pi) ^ 2) ^ p ≤ ((2 * Real.pi) ^ 2) ^ k :=
    pow_le_pow_right₀ invJet_one_le_two_pi_sq hp
  have hEF : 0 ≤ ENormSqFull k (seriesFunM c) := ENormSqFull_nonneg k _
  calc ((2 * Real.pi) ^ 2) ^ p * Work.Diff.STE.CSq p (fun κ => c κ i j)
      ≤ ((2 * Real.pi) ^ 2) ^ p * Work.Diff.STE.CSq k (fun κ => c κ i j) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ ((2 * Real.pi) ^ 2) ^ p * (Ck * ENormSqFull k (seriesFunM c)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ ((2 * Real.pi) ^ 2) ^ k * (Ck * ENormSqFull k (seriesFunM c)) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg hCk hEF)
    _ = ((2 * Real.pi) ^ 2) ^ k * Ck * ENormSqFull k (seriesFunM c) := by ring

/-- **The `H^p` energy of an entry of `seriesFunM c` is controlled by the top-level energy.** -/
lemma ENormSq_entry_le {n : ℕ} (k p : ℕ) (hp : p ≤ k) {Ck : ℝ} (hCk : 0 ≤ Ck)
    (hCk' : ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ κ : Fin n → ℤ, κ ∉ box n N → c κ = 0) → ∀ i j : Fin n,
      Work.Diff.STE.CSq k (fun m => c m i j) ≤ Ck * ENormSqFull k (seriesFunM c))
    {N : ℕ} {c : (Fin n → ℤ) → MatC n} (hc : ∀ κ : Fin n → ℤ, κ ∉ box n N → c κ = 0)
    (i j : Fin n) :
    Work.Diff.STE.ENormSq p (fun y : Fin n → ℝ => seriesFunM c y i j)
      ≤ (Fintype.card (Fin p → Fin n) : ℝ)
          * (((2 * Real.pi) ^ 2) ^ k * Ck * ENormSqFull k (seriesFunM c)) := by
  rw [Work.Diff.STE.ENormSq]
  calc ∑ l : Fin p → Fin n, ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdVec p l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ ^ 2
      ≤ ∑ _l : Fin p → Fin n,
          ((2 * Real.pi) ^ 2) ^ k * Ck * ENormSqFull k (seriesFunM c) :=
        Finset.sum_le_sum (fun l _ => int_pdVec_entry_le k p hp hCk hCk' hc i j l)
    _ = (Fintype.card (Fin p → Fin n) : ℝ)
          * (((2 * Real.pi) ^ 2) ^ k * Ck * ENormSqFull k (seriesFunM c)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The sup bound for one partial derivative of an entry of `seriesFunM c`.** -/
lemma pdVec_entry_sup_le {n s : ℕ} {Csup KA : ℝ} (hCsupnn : 0 ≤ Csup) (hKAnn : 0 ≤ KA)
    (hCsup : ∀ (c : (Fin n → ℤ) → ℂ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ Work.Diff.STE.flat.sob n
        * ‖c k‖ ^ 2) →
      ∀ x : Fin n → ℝ,
        ‖Work.Diff.STE.seriesFun c x‖
          ≤ Csup * Real.sqrt (Work.Diff.STE.CSq (Work.Diff.STE.flat.sob n) c))
    {Bs : ℝ} (hBs : 0 ≤ Bs) {N : ℕ} {c : (Fin n → ℤ) → MatC n}
    (hc : ∀ κ : Fin n → ℤ, κ ∉ box n N → c κ = 0)
    (hcsq : ∀ i j : Fin n,
      Work.Diff.STE.CSq s (fun m => c m i j) ≤ KA * ENormSqFull s (seriesFunM c))
    (hEF : ENormSqFull s (seriesFunM c) ≤ Bs ^ 2)
    (q : ℕ) (hq : q + Work.Diff.STE.flat.sob n ≤ s) (l : Fin q → Fin n) (i j : Fin n)
    (x : Fin n → ℝ) :
    ‖Work.Diff.STE.pdVec q l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖
      ≤ Csup * (2 * Real.pi) ^ s * Real.sqrt KA * (1 + Bs) ^ 2 := by
  have hd : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M * ‖c k i j‖) :=
    fun M => summable_moment_box c hc i j M
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = Work.Diff.STE.seriesFun (fun κ => c κ i j) := by
    funext y; rw [seriesFunM_apply]
  rw [hfun]
  have hY : 0 ≤ KA * ENormSqFull s (seriesFunM c) := mul_nonneg hKAnn (ENormSqFull_nonneg s _)
  have hY' : Work.Diff.STE.CSq s (fun κ => c κ i j)
      ≤ (KA * ENormSqFull s (seriesFunM c)) * (1 + Bs) ^ 2 := by
    refine (hcsq i j).trans ?_
    have h1 : (1 : ℝ) ≤ (1 + Bs) ^ 2 := by nlinarith
    nlinarith [hY, h1]
  have h := invJet_sup_pdVec_seriesFun_le (n := n) (s := s) (by omega : Work.Diff.STE.flat.sob n ≤ s)
    hd (Csup := Csup) (Y := KA * ENormSqFull s (seriesFunM c)) (Bs := Bs)
    hCsupnn hCsup hY hBs hY' q hq l x
  refine h.trans ?_
  have hsqrt : Real.sqrt (KA * ENormSqFull s (seriesFunM c)) ≤ Real.sqrt KA * Bs := by
    rw [Real.sqrt_mul hKAnn]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg KA)
    exact (Real.sqrt_le_sqrt hEF).trans (le_of_eq (Real.sqrt_sq hBs))
  have hc0 : 0 ≤ Csup * (2 * Real.pi) ^ s := mul_nonneg hCsupnn (by positivity)
  calc Csup * (2 * Real.pi) ^ s * Real.sqrt (KA * ENormSqFull s (seriesFunM c)) * (1 + Bs)
      ≤ Csup * (2 * Real.pi) ^ s * (Real.sqrt KA * Bs) * (1 + Bs) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        exact mul_le_mul_of_nonneg_left hsqrt hc0
    _ = Csup * (2 * Real.pi) ^ s * Real.sqrt KA * (Bs * (1 + Bs)) := by ring
    _ ≤ Csup * (2 * Real.pi) ^ s * Real.sqrt KA * (1 + Bs) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [hBs]


/-- The number of tuples of length `p` over `Fin n` grows with `p`. -/
lemma card_fun_le_card_fun {n p K : ℕ} (hn : 1 ≤ n) (hp : p ≤ K) :
    (Fintype.card (Fin p → Fin n) : ℝ) ≤ (Fintype.card (Fin K → Fin n) : ℝ) := by
  have h : Fintype.card (Fin p → Fin n) ≤ Fintype.card (Fin K → Fin n) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_le_pow_right hn hp
  exact_mod_cast h

theorem jetP_iteratedFDeriv_bound {n s : ℕ} (hn : 1 ≤ n) (hs : n + 5 ≤ s)
    (Bs : ℝ) (hBs : 0 ≤ Bs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k : Fin n → ℤ, k ∉ Work.Diff.STE.Flat.box n N → c k = 0) →
      Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 →
      (∀ (m : ℕ) (hm : m ≤ s + 1),
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
            ‖iteratedFDeriv ℝ m (Work.Diff.STE.flat.jetP c) x‖ ^ 2
          ≤ C * (1 + Bs ^ 2
              + Work.Diff.STE.Flat.ENormSqM (s + 1) (Work.Diff.STE.Flat.seriesFunM c)
              + Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c))) ∧
      (∀ (M : ℕ) (hM : M + 1 + Work.Diff.STE.flat.sob n ≤ s) (m : ℕ) (hm : m ≤ M)
        (x : Fin n → ℝ),
          ‖iteratedFDeriv ℝ m (Work.Diff.STE.flat.jetP c) x‖ ≤ C * (1 + Bs)) := by
  obtain ⟨KA, hKAnn, hKA⟩ := invJet_CSq_entry_le_uniform (n := n) (s + 2)
  obtain ⟨KA1, hKA1nn, hKA1⟩ := invJet_CSq_entry_le_uniform (n := n) s
  obtain ⟨K0, hK0nn, hK0⟩ := Work.Diff.STE.norm_seriesFun_le (ι := Fin n)
    (Work.Diff.STE.flat.sob n) (by simpa using n_lt_two_sob n)
  set cc : ℝ := (Fintype.card (Fin (s + 2) → Fin n) : ℝ) with hcc
  set c22 : ℝ := (Fintype.card (Fin n × Fin n) : ℝ) with hc22
  set c33 : ℝ := (Fintype.card (Fin n × Fin n × Fin n) : ℝ) with hc33
  set KE : ℝ := ((2 * Real.pi) ^ 2) ^ (s + 2) * KA with hKE
  set Q : ℝ := K0 * (2 * Real.pi) ^ s * Real.sqrt KA1 with hQ
  set KS : ℝ := (c22 + c33) * cc * Q with hKS
  set KL : ℝ := (2 * c22 * c22 * cc * cc + 2 * c33 * c33 * cc * cc * cc) * KE with hKL
  have hccnn : (0 : ℝ) ≤ cc := by rw [hcc]; exact Nat.cast_nonneg _
  have hc22nn : (0 : ℝ) ≤ c22 := by rw [hc22]; exact Nat.cast_nonneg _
  have hc33nn : (0 : ℝ) ≤ c33 := by rw [hc33]; exact Nat.cast_nonneg _
  have h2pinn : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h2pi2nn : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := pow_nonneg h2pinn 2
  have hKEnn : (0 : ℝ) ≤ KE := by
    rw [hKE]; exact mul_nonneg (pow_nonneg h2pi2nn (s + 2)) hKAnn
  have hQnn : (0 : ℝ) ≤ Q := by
    rw [hQ]
    exact mul_nonneg (mul_nonneg hK0nn (pow_nonneg h2pinn s)) (Real.sqrt_nonneg KA1)
  have hKSnn : (0 : ℝ) ≤ KS := by
    rw [hKS]; exact mul_nonneg (mul_nonneg (add_nonneg hc22nn hc33nn) hccnn) hQnn
  have hKLnn : (0 : ℝ) ≤ KL := by
    rw [hKL]
    exact mul_nonneg (add_nonneg (by positivity) (by positivity)) hKEnn
  refine ⟨(KL + KS) * (1 + Bs) ^ 2, by positivity, ?_⟩
  intro N c hc hE
  -- the two elementary energy comparisons at the top level
  have hEM0 : Work.Diff.STE.Flat.ENormSqM 0 (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 :=
    (ENormSqM_zero_le_ENormSqFull s _).trans hE
  have hEFtop : Work.Diff.STE.Flat.ENormSqFull (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
      ≤ 1 + Bs ^ 2 + Work.Diff.STE.Flat.ENormSqM (s + 1) (Work.Diff.STE.Flat.seriesFunM c)
        + Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c) := by
    rw [Work.Diff.STE.Flat.ENormSqFull]
    have h1 : (0 : ℝ) ≤ Work.Diff.STE.Flat.ENormSqM (s + 1) (Work.Diff.STE.Flat.seriesFunM c) :=
      ENormSqM_nonneg _ _
    linarith
  constructor
  · -- ===== the L² bound =====
    intro m hm
    have hA : ∀ i j : Fin n,
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ ^ 2
        ≤ cc * cc * KE * ENormSqFull (s + 2) (seriesFunM c) := by
      intro i j
      have hf : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => seriesFunM c y i j) :=
        contDiff_entry_seriesFunM N c hc i j
      have h1 := int_iteratedFDeriv_sq_le_ENormSq_aux m _ hf
      have h2 := ENormSq_entry_le (s + 2) m (by omega) hKAnn hKA hc i j
      have h3 : (Fintype.card (Fin m → Fin n) : ℝ) ≤ cc := by
        rw [hcc]; exact card_fun_le_card_fun hn (by omega)
      have hEFnn : (0 : ℝ) ≤ ENormSqFull (s + 2) (seriesFunM c) := ENormSqFull_nonneg _ _
      have hXnn : (0 : ℝ) ≤ KE * ENormSqFull (s + 2) (seriesFunM c) := mul_nonneg hKEnn hEFnn
      calc ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
            ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ ^ 2
          ≤ (Fintype.card (Fin m → Fin n) : ℝ)
              * Work.Diff.STE.ENormSq m (fun y : Fin n → ℝ => seriesFunM c y i j) := h1
        _ ≤ (Fintype.card (Fin m → Fin n) : ℝ)
              * ((Fintype.card (Fin m → Fin n) : ℝ)
                  * (((2 * Real.pi) ^ 2) ^ (s + 2) * KA
                      * ENormSqFull (s + 2) (seriesFunM c))) := by
            rw [← hKE]
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ cc * (cc * (((2 * Real.pi) ^ 2) ^ (s + 2) * KA
                * ENormSqFull (s + 2) (seriesFunM c))) :=
            mul_le_mul h3 (mul_le_mul_of_nonneg_right h3 hXnn) (by positivity) hccnn
        _ = cc * cc * KE * ENormSqFull (s + 2) (seriesFunM c) := by rw [hKE]; ring
    have hB : ∀ a i j : Fin n,
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ‖iteratedFDeriv ℝ m
            (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖ ^ 2
        ≤ cc * cc * cc * KE * ENormSqFull (s + 2) (seriesFunM c) := by
      intro a i j
      have hf : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) :=
        contDiff_pd_entry_seriesFunM N c hc a i j
      have h1 := int_iteratedFDeriv_sq_le_ENormSq_aux m _ hf
      have h2 := ENormSq_pd_le m a (fun y : Fin n → ℝ => seriesFunM c y i j)
      have h3 := ENormSq_entry_le (s + 2) (m + 1) (by omega) hKAnn hKA hc i j
      have h4 : (Fintype.card (Fin m → Fin n) : ℝ) ≤ cc := by
        rw [hcc]; exact card_fun_le_card_fun hn (by omega)
      have h5 : (Fintype.card (Fin (m + 1) → Fin n) : ℝ) ≤ cc := by
        rw [hcc]; exact card_fun_le_card_fun hn (by omega)
      have hEFnn : (0 : ℝ) ≤ ENormSqFull (s + 2) (seriesFunM c) := ENormSqFull_nonneg _ _
      have hXnn : (0 : ℝ) ≤ KE * ENormSqFull (s + 2) (seriesFunM c) := mul_nonneg hKEnn hEFnn
      calc ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
            ‖iteratedFDeriv ℝ m
              (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖ ^ 2
          ≤ (Fintype.card (Fin m → Fin n) : ℝ)
              * Work.Diff.STE.ENormSq m
                  (Work.Diff.STE.pd a (fun y : Fin n → ℝ => seriesFunM c y i j)) := h1
        _ ≤ (Fintype.card (Fin m → Fin n) : ℝ)
              * ((Fintype.card (Fin m → Fin n) : ℝ)
                  * Work.Diff.STE.ENormSq (m + 1) (fun y : Fin n → ℝ => seriesFunM c y i j)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ (Fintype.card (Fin m → Fin n) : ℝ)
              * ((Fintype.card (Fin m → Fin n) : ℝ)
                  * ((Fintype.card (Fin (m + 1) → Fin n) : ℝ)
                      * (((2 * Real.pi) ^ 2) ^ (s + 2) * KA
                          * ENormSqFull (s + 2) (seriesFunM c)))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [← hKE]
            exact h3
        _ ≤ cc * (cc * (cc * (((2 * Real.pi) ^ 2) ^ (s + 2) * KA
                * ENormSqFull (s + 2) (seriesFunM c)))) := by
            refine mul_le_mul h4 ?_ (by positivity) hccnn
            refine mul_le_mul h4 ?_ (by positivity) hccnn
            exact mul_le_mul_of_nonneg_right h5 hXnn
        _ = cc * cc * cc * KE * ENormSqFull (s + 2) (seriesFunM c) := by rw [hKE]; ring
    set S1 : (Fin n → ℝ) → ℝ := fun x => ∑ t : Fin n × Fin n,
      ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y t.1 t.2) x‖ with hS1
    set S2 : (Fin n → ℝ) → ℝ := fun x => ∑ t : Fin n × Fin n × Fin n,
      ‖iteratedFDeriv ℝ m
        (fun y : Fin n → ℝ => Work.Diff.STE.pd t.1 (fun z => seriesFunM c z t.2.1 t.2.2) y) x‖
      with hS2
    have hcontS1 : Continuous (fun x : Fin n → ℝ => S1 x ^ 2) := by
      rw [hS1]
      refine Continuous.pow ?_ 2
      exact continuous_finsetSum _ (fun t _ =>
        ((contDiff_entry_seriesFunM N c hc t.1 t.2).continuous_iteratedFDeriv (by simp)).norm)
    have hcontS2 : Continuous (fun x : Fin n → ℝ => S2 x ^ 2) := by
      rw [hS2]
      refine Continuous.pow ?_ 2
      exact continuous_finsetSum _ (fun t _ =>
        ((contDiff_pd_entry_seriesFunM N c hc t.1 t.2.1 t.2.2).continuous_iteratedFDeriv
          (by simp)).norm)
    have hcontL : Continuous (fun x : Fin n → ℝ =>
        ‖iteratedFDeriv ℝ m (jetP c) x‖ ^ 2) :=
      ((contDiff_jetP N c hc).continuous_iteratedFDeriv (by simp)).norm.pow 2
    have hS1' : ∀ x : Fin n → ℝ, S1 x = ∑ i : Fin n, ∑ j : Fin n,
        ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ := by
      intro x
      rw [hS1]
      beta_reduce
      exact Fintype.sum_prod_type
        (f := fun t : Fin n × Fin n =>
          ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y t.1 t.2) x‖)
    have hS2' : ∀ x : Fin n → ℝ, S2 x = ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        ‖iteratedFDeriv ℝ m
          (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖ := by
      intro x
      rw [hS2]
      beta_reduce
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl (fun a _ => Fintype.sum_prod_type
        (f := fun t : Fin n × Fin n =>
          ‖iteratedFDeriv ℝ m
            (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z t.1 t.2) y) x‖))
    have hpt : ∀ x : Fin n → ℝ, ‖iteratedFDeriv ℝ m (jetP c) x‖ ^ 2
        ≤ 2 * S1 x ^ 2 + 2 * S2 x ^ 2 := by
      intro x
      have h := norm_iteratedFDeriv_jetP_le N c hc m x
      set A : ℝ := ∑ i : Fin n, ∑ j : Fin n,
        ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ with hAset
      set Bv : ℝ := ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        ‖iteratedFDeriv ℝ m
          (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖ with hBset
      have hmain : ‖iteratedFDeriv ℝ m (jetP c) x‖ ≤ A + Bv := by
        rw [hAset, hBset]; exact h
      have hAnn : (0 : ℝ) ≤ A := by
        rw [hAset]
        exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
      have hBnn : (0 : ℝ) ≤ Bv := by
        rw [hBset]
        exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun i _ =>
          Finset.sum_nonneg (fun j _ => norm_nonneg _)))
      have hgoal : 2 * S1 x ^ 2 + 2 * S2 x ^ 2 = 2 * A ^ 2 + 2 * Bv ^ 2 := by
        rw [hS1' x, hS2' x, ← hAset, ← hBset]
      rw [hgoal]
      nlinarith [hmain, hAnn, hBnn, norm_nonneg (iteratedFDeriv ℝ m (jetP c) x),
        sq_nonneg (A - Bv)]
    have hcs1 : ∫ x in Work.Diff.STE.unitCube (ι := Fin n), S1 x ^ 2
        ≤ c22 * ∑ t : Fin n × Fin n,
            ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
              ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y t.1 t.2) x‖ ^ 2 := by
      have h := JetComp.integral_sq_sum_le
        (a := fun t : Fin n × Fin n => fun x : Fin n → ℝ =>
          ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y t.1 t.2) x‖)
        (fun t => ((contDiff_entry_seriesFunM N c hc t.1 t.2).continuous_iteratedFDeriv
          (by simp)).norm) (fun t x => norm_nonneg _)
      rw [hS1, hc22]
      exact h
    have hcs2 : ∫ x in Work.Diff.STE.unitCube (ι := Fin n), S2 x ^ 2
        ≤ c33 * ∑ t : Fin n × Fin n × Fin n,
            ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
              ‖iteratedFDeriv ℝ m
                (fun y : Fin n → ℝ => Work.Diff.STE.pd t.1
                  (fun z => seriesFunM c z t.2.1 t.2.2) y) x‖ ^ 2 := by
      have h := JetComp.integral_sq_sum_le
        (a := fun t : Fin n × Fin n × Fin n => fun x : Fin n → ℝ =>
          ‖iteratedFDeriv ℝ m
            (fun y : Fin n → ℝ => Work.Diff.STE.pd t.1
              (fun z => seriesFunM c z t.2.1 t.2.2) y) x‖)
        (fun t => ((contDiff_pd_entry_seriesFunM N c hc t.1 t.2.1 t.2.2).continuous_iteratedFDeriv
          (by simp)).norm) (fun t x => norm_nonneg _)
      rw [hS2, hc33]
      exact h
    have hsumA : ∑ t : Fin n × Fin n,
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y t.1 t.2) x‖ ^ 2
        ≤ c22 * (cc * cc * KE * ENormSqFull (s + 2) (seriesFunM c)) := by
      calc ∑ t : Fin n × Fin n,
            ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
              ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y t.1 t.2) x‖ ^ 2
          ≤ ∑ _t : Fin n × Fin n, cc * cc * KE * ENormSqFull (s + 2) (seriesFunM c) :=
            Finset.sum_le_sum (fun t _ => hA t.1 t.2)
        _ = c22 * (cc * cc * KE * ENormSqFull (s + 2) (seriesFunM c)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc22]
    have hsumB : ∑ t : Fin n × Fin n × Fin n,
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ‖iteratedFDeriv ℝ m
            (fun y : Fin n → ℝ => Work.Diff.STE.pd t.1
              (fun z => seriesFunM c z t.2.1 t.2.2) y) x‖ ^ 2
        ≤ c33 * (cc * cc * cc * KE * ENormSqFull (s + 2) (seriesFunM c)) := by
      calc ∑ t : Fin n × Fin n × Fin n,
            ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
              ‖iteratedFDeriv ℝ m
                (fun y : Fin n → ℝ => Work.Diff.STE.pd t.1
                  (fun z => seriesFunM c z t.2.1 t.2.2) y) x‖ ^ 2
          ≤ ∑ _t : Fin n × Fin n × Fin n,
              cc * cc * cc * KE * ENormSqFull (s + 2) (seriesFunM c) :=
            Finset.sum_le_sum (fun t _ => hB t.1 t.2.1 t.2.2)
        _ = c33 * (cc * cc * cc * KE * ENormSqFull (s + 2) (seriesFunM c)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc33]
    have hi1 : Integrable (fun x : Fin n → ℝ => S1 x ^ 2)
        (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
      JetComp.integrableOn_unitCube_of_continuous hcontS1
    have hi2 : Integrable (fun x : Fin n → ℝ => S2 x ^ 2)
        (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
      JetComp.integrableOn_unitCube_of_continuous hcontS2
    have hInt : ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ‖iteratedFDeriv ℝ m (jetP c) x‖ ^ 2
        ≤ 2 * (∫ x in Work.Diff.STE.unitCube (ι := Fin n), S1 x ^ 2)
          + 2 * (∫ x in Work.Diff.STE.unitCube (ι := Fin n), S2 x ^ 2) := by
      have h1 : Integrable (fun x : Fin n → ℝ => ‖iteratedFDeriv ℝ m (jetP c) x‖ ^ 2)
          (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
        JetComp.integrableOn_unitCube_of_continuous hcontL
      have h2 : Integrable (fun x : Fin n → ℝ => 2 * S1 x ^ 2 + 2 * S2 x ^ 2)
          (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
        JetComp.integrableOn_unitCube_of_continuous
          ((hcontS1.const_mul 2).add (hcontS2.const_mul 2))
      refine (MeasureTheory.setIntegral_mono_on h1 h2 (JetComp.measSet_unitCube n)
        (fun x _ => hpt x)).trans (le_of_eq ?_)
      rw [MeasureTheory.integral_add (hi1.const_mul 2) (hi2.const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    calc ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖iteratedFDeriv ℝ m (jetP c) x‖ ^ 2
        ≤ 2 * (∫ x in Work.Diff.STE.unitCube (ι := Fin n), S1 x ^ 2)
          + 2 * (∫ x in Work.Diff.STE.unitCube (ι := Fin n), S2 x ^ 2) := hInt
      _ ≤ 2 * (c22 * ∑ t : Fin n × Fin n,
              ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
                ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y t.1 t.2) x‖ ^ 2)
          + 2 * (c33 * ∑ t : Fin n × Fin n × Fin n,
              ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
                ‖iteratedFDeriv ℝ m
                  (fun y : Fin n → ℝ => Work.Diff.STE.pd t.1
                    (fun z => seriesFunM c z t.2.1 t.2.2) y) x‖ ^ 2) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left hcs1 (by norm_num)
          · exact mul_le_mul_of_nonneg_left hcs2 (by norm_num)
      _ ≤ 2 * (c22 * (c22 * (cc * cc * KE * ENormSqFull (s + 2) (seriesFunM c))))
          + 2 * (c33 * (c33 * (cc * cc * cc * KE * ENormSqFull (s + 2) (seriesFunM c)))) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumA hc22nn) (by norm_num)
          · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumB hc33nn) (by norm_num)
      _ = KL * ENormSqFull (s + 2) (seriesFunM c) := by rw [hKL]; ring
      _ ≤ (KL + KS) * (1 + Bs) ^ 2
            * (1 + Bs ^ 2 + Work.Diff.STE.Flat.ENormSqM (s + 1) (Work.Diff.STE.Flat.seriesFunM c)
              + Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c)) := by
          have hZnn : (0 : ℝ) ≤ 1 + Bs ^ 2
              + Work.Diff.STE.Flat.ENormSqM (s + 1) (Work.Diff.STE.Flat.seriesFunM c)
              + Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c) := by
            have h1 : (0 : ℝ) ≤ Work.Diff.STE.Flat.ENormSqM (s + 1)
                (Work.Diff.STE.Flat.seriesFunM c) := ENormSqM_nonneg _ _
            have h2 : (0 : ℝ) ≤ Work.Diff.STE.Flat.ENormSqM (s + 2)
                (Work.Diff.STE.Flat.seriesFunM c) := ENormSqM_nonneg _ _
            nlinarith [sq_nonneg Bs]
          refine mul_le_mul ?_ hEFtop (ENormSqFull_nonneg _ _) ?_
          · have h1 : KL ≤ KL * (1 + Bs) ^ 2 :=
              le_mul_of_one_le_right hKLnn (by nlinarith)
            have h2 : KL ≤ KL + KS := le_add_of_nonneg_right hKSnn
            exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
          · exact mul_nonneg (add_nonneg hKLnn hKSnn) (by positivity)
  · -- ===== the sup bound =====
    intro M hM m hm x
    have hA : ∀ i j : Fin n,
        ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y i j) x‖
          ≤ cc * (Q * (1 + Bs) ^ 2) := by
      intro i j
      have hb : ∀ l : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖
            ≤ Q * (1 + Bs) ^ 2 := by
        intro l
        have h := pdVec_entry_sup_le (n := n) (s := s) (Csup := K0) (KA := KA1) hK0nn hKA1nn
          (fun d hd => hK0 d hd) hBs hc (fun i' j' => hKA1 N c hc i' j') hE m (by omega) l i j x
        rw [← hQ] at h
        exact h
      have h3 : (Fintype.card (Fin m → Fin n) : ℝ) ≤ cc := by
        rw [hcc]; exact card_fun_le_card_fun hn (by omega)
      calc ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y i j) x‖
          ≤ ∑ l : Fin m → Fin n,
              ‖Work.Diff.STE.pdVec m l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ :=
            norm_iteratedFDeriv_le_sum_pdVec m _ (contDiff_entry_seriesFunM N c hc i j) x
        _ ≤ ∑ _l : Fin m → Fin n, Q * (1 + Bs) ^ 2 :=
            Finset.sum_le_sum (fun l _ => hb l)
        _ = (Fintype.card (Fin m → Fin n) : ℝ) * (Q * (1 + Bs) ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ cc * (Q * (1 + Bs) ^ 2) := mul_le_mul_of_nonneg_right h3 (by positivity)
    have hB : ∀ a i j : Fin n,
        ‖iteratedFDeriv ℝ m
          (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖
          ≤ cc * (Q * (1 + Bs) ^ 2) := by
      intro a i j
      have hb : ∀ l : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m l
            (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖
            ≤ Q * (1 + Bs) ^ 2 := by
        intro l
        have h := pdVec_entry_sup_le (n := n) (s := s) (Csup := K0) (KA := KA1) hK0nn hKA1nn
          (fun d hd => hK0 d hd) hBs hc (fun i' j' => hKA1 N c hc i' j') hE (m + 1)
          (by omega) (Fin.append l ![a]) i j x
        rw [pdVec_pd_eq] at h
        rw [← hQ] at h
        exact h
      have h3 : (Fintype.card (Fin m → Fin n) : ℝ) ≤ cc := by
        rw [hcc]; exact card_fun_le_card_fun hn (by omega)
      calc ‖iteratedFDeriv ℝ m
            (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖
          ≤ ∑ l : Fin m → Fin n,
              ‖Work.Diff.STE.pdVec m l
                (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖ :=
            norm_iteratedFDeriv_le_sum_pdVec m _
              (contDiff_pd_entry_seriesFunM N c hc a i j) x
        _ ≤ ∑ _l : Fin m → Fin n, Q * (1 + Bs) ^ 2 :=
            Finset.sum_le_sum (fun l _ => hb l)
        _ = (Fintype.card (Fin m → Fin n) : ℝ) * (Q * (1 + Bs) ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ cc * (Q * (1 + Bs) ^ 2) := mul_le_mul_of_nonneg_right h3 (by positivity)
    have hQ2nn : (0 : ℝ) ≤ Q * (1 + Bs) ^ 2 := by positivity
    calc ‖iteratedFDeriv ℝ m (jetP c) x‖
        ≤ (∑ i : Fin n, ∑ j : Fin n,
              ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y i j) x‖)
            + ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              ‖iteratedFDeriv ℝ m
                (fun y : Fin n → ℝ => Work.Diff.STE.pd a (fun z => seriesFunM c z i j) y) x‖ :=
          norm_iteratedFDeriv_jetP_le N c hc m x
      _ ≤ (∑ _i : Fin n, ∑ _j : Fin n, cc * (Q * (1 + Bs) ^ 2))
            + ∑ _a : Fin n, ∑ _i : Fin n, ∑ _j : Fin n, cc * (Q * (1 + Bs) ^ 2) := by
          refine add_le_add ?_ ?_
          · exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hA i j))
          · exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun i _ =>
              Finset.sum_le_sum (fun j _ => hB a i j)))
      _ = (c22 + c33) * cc * (Q * (1 + Bs) ^ 2) := by
          rw [hc22, hc33]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin,
            Fintype.card_prod]
          push_cast
          ring
      _ = KS * (1 + Bs) ^ 2 := by rw [hKS]; ring
      _ ≤ (KL + KS) * (1 + Bs) ^ 2 * (1 + Bs) := by
          have hA1 : KS ≤ KL + KS := le_add_of_nonneg_left hKLnn
          have h1 : KS * (1 + Bs) ^ 2 ≤ (KL + KS) * (1 + Bs) ^ 2 :=
            mul_le_mul_of_nonneg_right hA1 (by positivity)
          refine h1.trans ?_
          have h3 : (1 : ℝ) ≤ 1 + Bs := by linarith
          have hnn : (0 : ℝ) ≤ (KL + KS) * (1 + Bs) ^ 2 := by positivity
          calc (KL + KS) * (1 + Bs) ^ 2 = (KL + KS) * (1 + Bs) ^ 2 * 1 := by ring
            _ ≤ (KL + KS) * (1 + Bs) ^ 2 * (1 + Bs) :=
                mul_le_mul_of_nonneg_left h3 hnn

end

end Work.Diff.STE.flat
