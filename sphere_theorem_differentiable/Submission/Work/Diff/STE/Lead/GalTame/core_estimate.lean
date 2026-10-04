import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Lead.GalTame.prod_interp_le
import Submission.Work.Diff.STE.pdList_mul_sub
import Submission.Work.Diff.STE.commutator_pd
import Submission.Work.Diff.STE.commutator_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The tame (`L²`) estimate for the transport term `Σ_{cd} A_{cd} ∂_c∂_d u`

`Work.Diff.STE.Lead.GalTame.core_estimate` bounds the `H^{k-1}` energy of the transport term
`w = Σ_c Σ_d A c d · ∂_c ∂_d u` by the sup bounds of `A`, `u` and the `H^{k+1}` energies of `A`
and `u`:

`ENormSq (k-1) w ≤ C (1 + CA)² (1 + CU)² (1 + KA + U)`.

The proof is the Moser/Leibniz argument, with the sharp product interpolation
`Work.Diff.STE.Lead.GalTame.prod_interp_le` as the only analytic input:

* `ENormSq (k-1) w` is the sum over `l : Fin (k-1) → ι` of `∫ ‖∂^l w‖²`;
* the full iterated Leibniz rule (`pdList_mul_splits`) expands `∂^l (A c d · ∂_c∂_d u)` as the sum
  of `∂^a (A c d) · ∂^{b+2} u` over the `2^{k-1}` splits `(a, b)` of the list of directions `l`, and
  `Σ_c Σ_d` turns this into a finite sum whose index set is `(ι × ι) × Fin (2^{k-1})`;
* Cauchy–Schwarz on `L²` (`integral_norm_sum_sq_le`) and `prod_interp_le` (applied at level
  `k+1 = a + (b+2)`, with `S = CA + CU`, `A = KA`, `B = U`) bound every term by
  `Cint · S² (KA + U)`;
* the cardinalities `card (Fin (k-1) → ι) = N^{k-1}` and `card ((ι × ι) × Fin 2^{k-1}) = N²2^{k-1}`
  produce the final constant, and `CA + CU ≤ (1+CA)(1+CU)` converts `S² (KA+U)` into the stated
  shape.
-/

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary helpers -/

/-- **`L²` bound for a finite sum** (Cauchy–Schwarz, integrated). -/
private lemma integral_norm_sum_sq_le {β : Type*} [Fintype β] (f : β → (ι → ℝ) → ℂ)
    (hf : ∀ b, Continuous (f b)) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖∑ b, f b x‖ ^ 2
      ≤ (Fintype.card β : ℝ) * ∑ b, ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f b x‖ ^ 2 := by
  have hpt : ∀ x : ι → ℝ, ‖∑ b, f b x‖ ^ 2
      ≤ (Fintype.card β : ℝ) * ∑ b, ‖f b x‖ ^ 2 := by
    intro x
    have h1 : ‖∑ b, f b x‖ ≤ ∑ b, ‖f b x‖ := norm_sum_le _ _
    have h3 : (∑ b : β, ‖f b x‖) ^ 2 ≤ (Fintype.card β : ℝ) * ∑ b : β, ‖f b x‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset β))
        (f := fun b => ‖f b x‖)
    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h3
  have hcont1 : Continuous fun x : ι → ℝ => ‖∑ b, f b x‖ ^ 2 :=
    (continuous_finset_sum _ (fun b _ => hf b)).norm.pow 2
  have hcont2 : Continuous fun x : ι → ℝ =>
      (Fintype.card β : ℝ) * ∑ b, ‖f b x‖ ^ 2 :=
    continuous_const.mul (continuous_finset_sum _ (fun b _ => (hf b).norm.pow 2))
  calc ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖∑ b, f b x‖ ^ 2
      ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), (Fintype.card β : ℝ) * ∑ b, ‖f b x‖ ^ 2 :=
        integral_mono (Work.Diff.STE.cm_integrableOn_unitCube_of_continuous hcont1)
          (Work.Diff.STE.cm_integrableOn_unitCube_of_continuous hcont2) hpt
    _ = (Fintype.card β : ℝ)
          * ∫ x in Work.Diff.STE.unitCube (ι := ι), ∑ b, ‖f b x‖ ^ 2 :=
        integral_const_mul _ _
    _ = (Fintype.card β : ℝ)
          * ∑ b, ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖f b x‖ ^ 2 := by
        rw [integral_finset_sum]
        exact fun b _ =>
          Work.Diff.STE.cm_integrableOn_unitCube_of_continuous ((hf b).norm.pow 2)

/-- Evaluation of a list of functions as a `Fin`-indexed sum. -/
private lemma list_sum_map_eq_sum_fin {α : Type*} (L : List α) (g : α → ℂ) :
    (L.map g).sum = ∑ i : Fin L.length, g (L.get i) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [List.map_cons, List.sum_cons, ih]
      change g a + ∑ i : Fin L.length, g (L.get i) = ∑ i : Fin (L.length + 1), g ((a :: L).get i)
      rw [Fin.sum_univ_succ]
      simp

/-- `pdVec` along the entries of a list is `pdList`. -/
lemma pdVec_get_eq_pdList_self (q : List ι) (f : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pdVec q.length (fun i => q.get i) f = Work.Diff.STE.pdList q f := by
  have h : List.ofFn (fun i : Fin q.length => q.get i) = q := List.ofFn_get q
  simp only [Work.Diff.STE.pdVec, h]

/-- `pdVec` along the entries of a list of the same length is `pdList`. -/
lemma pdVec_get_eq_pdList_gen {n : ℕ} {q : List ι} (hlen : q.length = n)
    (f : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pdVec n (fun i : Fin n => q.get (Fin.cast hlen.symm i)) f
      = Work.Diff.STE.pdList q f := by
  have hq : List.ofFn (fun i : Fin n => q.get (Fin.cast hlen.symm i)) = q :=
    (List.ofFn_congr hlen q.get).symm.trans (List.ofFn_get q)
  simp only [Work.Diff.STE.pdVec, hq]

/-- Iterated partial derivatives of a smooth function are continuous. -/
lemma continuous_pdList_of_contDiff {f : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f) (q : List ι) :
    Continuous (Work.Diff.STE.pdList q f) :=
  (Work.Diff.STE.cm_contDiff_pdList q 1 f (hf.of_le (WithTop.coe_le_coe.mpr le_top))).continuous

/-- Iterated partial derivatives of a smooth function are differentiable. -/
lemma differentiable_pdList_of_contDiff {f : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f) (q : List ι) :
    Differentiable ℝ (Work.Diff.STE.pdList q f) :=
  ((Work.Diff.STE.cm_contDiff_pdList q 1 f (hf.of_le (WithTop.coe_le_coe.mpr le_top)))).differentiable
    (by norm_num)

/-- A partial derivative of a smooth function is smooth. -/
lemma contDiff_pd_top' {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd i f) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ f x) (Pi.single i (1 : ℝ))) := by
    simpa [Function.comp_def, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ ℂ (Pi.single i (1 : ℝ))).contDiff.comp h
  exact h2

/-- Two partial derivatives of a smooth function are smooth. -/
lemma contDiff_pd_pd {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c d : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd c (Work.Diff.STE.pd d f)) :=
  contDiff_pd_top' (contDiff_pd_top' hf d) c

/-! ## The full iterated Leibniz rule

`pdList_mul_sub_aux` gives the *difference* form with the filtered splits `splitsNE`; adding back
the single missing term `([], l)` (`Work.Diff.STE.splitsNE_sum_add`) gives the full Leibniz rule,
and `list_sum_map_eq_sum_fin` turns the `List.sum` into a `Finset.sum` over `Fin (splits l).length`.
-/

lemma pdList_mul_splits (l : List ι) (F g : (ι → ℝ) → ℂ)
    (hF : ∀ q, List.Sublist q l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q F))
    (hg : ∀ q, List.Sublist q l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q g)) :
    Work.Diff.STE.pdList l (fun z => F z * g z)
      = fun z => ∑ i : Fin (Work.Diff.STE.splits l).length,
          Work.Diff.STE.pdList ((Work.Diff.STE.splits l).get i).1 F z
            * Work.Diff.STE.pdList ((Work.Diff.STE.splits l).get i).2 g z := by
  funext y
  have h := congrFun (Work.Diff.STE.pdList_mul_sub_aux l F g hF hg) y
  rw [Work.Diff.STE.listEval_map_eq] at h
  have hφ : Work.Diff.STE.PhiL F g ([], l) y = F y * Work.Diff.STE.pdList l g y := by
    simp [Work.Diff.STE.PhiL, Work.Diff.STE.pdList]
  have h2 := Work.Diff.STE.splitsNE_sum_add l (fun p => Work.Diff.STE.PhiL F g p y)
  rw [hφ] at h2
  have hsum : Work.Diff.STE.pdList l (fun z => F z * g z) y
      = ((Work.Diff.STE.splits l).map (fun p => Work.Diff.STE.PhiL F g p y)).sum := by
    calc Work.Diff.STE.pdList l (fun z => F z * g z) y
        = (Work.Diff.STE.pdList l (fun z => F z * g z) y
            - F y * Work.Diff.STE.pdList l g y) + F y * Work.Diff.STE.pdList l g y := by ring
      _ = ((Work.Diff.STE.splitsNE l).map (fun p => Work.Diff.STE.PhiL F g p y)).sum
            + F y * Work.Diff.STE.pdList l g y := by rw [h]
      _ = ((Work.Diff.STE.splits l).map (fun p => Work.Diff.STE.PhiL F g p y)).sum := h2
  rw [hsum, list_sum_map_eq_sum_fin]
  simp only [Work.Diff.STE.PhiL, Pi.mul_apply]

/-! ## The Leibniz terms of the transport expansion -/

/-- One Leibniz term of `∂^l (A c d · ∂_c∂_d u)`: the `i`-th split `p` of the list `l` puts the
directions `p.1` on `A c d` and the remaining directions `p.2` (together with `∂_c∂_d`) on `u`. -/
def leibTerm (A : ι → ι → (ι → ℝ) → ℂ) (u : (ι → ℝ) → ℂ) (l : List ι)
    (b : (ι × ι) × Fin (Work.Diff.STE.splits l).length) : (ι → ℝ) → ℂ :=
  fun z => Work.Diff.STE.pdList ((Work.Diff.STE.splits l).get b.2).1 (A b.1.1 b.1.2) z
    * Work.Diff.STE.pdList ((Work.Diff.STE.splits l).get b.2).2
        (Work.Diff.STE.pd b.1.1 (Work.Diff.STE.pd b.1.2 u)) z

lemma continuous_leibTerm {A : ι → ι → (ι → ℝ) → ℂ} {u : (ι → ℝ) → ℂ}
    (hAsm : ∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d))
    (husm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u) (l : List ι)
    (b : (ι × ι) × Fin (Work.Diff.STE.splits l).length) :
    Continuous (leibTerm A u l b) :=
  (continuous_pdList_of_contDiff (hAsm b.1.1 b.1.2) _).mul
    (continuous_pdList_of_contDiff (contDiff_pd_pd husm b.1.1 b.1.2) _)

/-- **The Leibniz expansion of the transport term**, per multi-index `l`:
`∂^l (Σ_{cd} A c d ∂_c∂_d u)` is the sum of the `2^{|l|}` Leibniz terms of `leibTerm`. -/
lemma pdVec_transport_eq_sum {A : ι → ι → (ι → ℝ) → ℂ} {u : (ι → ℝ) → ℂ}
    (hAsm : ∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d))
    (husm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u) (l : List ι) :
    Work.Diff.STE.pdList l (fun z => ∑ c, ∑ d,
        A c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) z)
      = fun z => ∑ b : (ι × ι) × Fin (Work.Diff.STE.splits l).length,
          leibTerm A u l b z := by
  have hw1 : (fun z => ∑ c, ∑ d, A c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) z)
      = fun z => ∑ q : ι × ι,
          A q.1 q.2 z * Work.Diff.STE.pd q.1 (Work.Diff.STE.pd q.2 u) z := by
    funext z
    rw [Fintype.sum_prod_type]
  have h2 : Work.Diff.STE.pdList l (fun z => ∑ c, ∑ d,
        A c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) z)
      = fun z => ∑ q : ι × ι, Work.Diff.STE.pdList l
          (fun y => A q.1 q.2 y * Work.Diff.STE.pd q.1 (Work.Diff.STE.pd q.2 u) y) z := by
    rw [hw1]
    exact Work.Diff.STE.cm_pdList_sum l (Finset.univ : Finset (ι × ι)) _
      (fun q _ q' _ _ => differentiable_pdList_of_contDiff
        ((hAsm q.1 q.2).mul (contDiff_pd_pd husm q.1 q.2)) q')
  have h3 : ∀ q : ι × ι,
      Work.Diff.STE.pdList l
          (fun y => A q.1 q.2 y * Work.Diff.STE.pd q.1 (Work.Diff.STE.pd q.2 u) y)
        = fun z => ∑ i : Fin (Work.Diff.STE.splits l).length,
            Work.Diff.STE.pdList ((Work.Diff.STE.splits l).get i).1 (A q.1 q.2) z
              * Work.Diff.STE.pdList ((Work.Diff.STE.splits l).get i).2
                  (Work.Diff.STE.pd q.1 (Work.Diff.STE.pd q.2 u)) z := by
    intro q
    exact pdList_mul_splits l (A q.1 q.2) (Work.Diff.STE.pd q.1 (Work.Diff.STE.pd q.2 u))
      (fun q' _ _ => differentiable_pdList_of_contDiff (hAsm q.1 q.2) q')
      (fun q' _ _ => differentiable_pdList_of_contDiff (contDiff_pd_pd husm q.1 q.2) q')
  rw [h2]
  funext z
  have hstep1 : ∀ x : ι × ι,
      (∑ i : Fin (Work.Diff.STE.splits l).length, leibTerm A u l (x, i) z)
        = Work.Diff.STE.pdList l
            (fun y => A x.1 x.2 y * Work.Diff.STE.pd x.1 (Work.Diff.STE.pd x.2 u) y) z := by
    intro x
    rw [h3 x]
    simp only [leibTerm]
  calc (∑ x : ι × ι, Work.Diff.STE.pdList l
        (fun y => A x.1 x.2 y * Work.Diff.STE.pd x.1 (Work.Diff.STE.pd x.2 u) y) z)
      = ∑ x : ι × ι, ∑ i : Fin (Work.Diff.STE.splits l).length, leibTerm A u l (x, i) z :=
        Finset.sum_congr rfl (fun x _ => (hstep1 x).symm)
    _ = ∑ b : (ι × ι) × Fin (Work.Diff.STE.splits l).length, leibTerm A u l b z :=
        (Fintype.sum_prod_type (f := fun b : (ι × ι) × Fin (Work.Diff.STE.splits l).length =>
          leibTerm A u l b z)).symm

end

/-! ## The estimate -/

theorem core_estimate {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : ι → ι → (ι → ℝ) → ℂ) (u : (ι → ℝ) → ℂ) (CA CU KA U : ℝ),
        (∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d)) →
        (∀ c d, Work.Diff.STE.Periodic1 (A c d)) →
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u →
        Work.Diff.STE.Periodic1 u →
        0 ≤ CA → 0 ≤ CU → 0 ≤ KA → 0 ≤ U →
        (∀ (c d : ι) (z : ι → ℝ), ‖A c d z‖ ≤ CA) →
        (∀ z : ι → ℝ, ‖u z‖ ≤ CU) →
        (∀ c d : ι, Work.Diff.STE.ENormSq (k + 1) (A c d) ≤ KA) →
        Work.Diff.STE.ENormSq (k + 1) u ≤ U →
        Work.Diff.STE.ENormSq (k - 1)
            (fun z : ι → ℝ => ∑ c, ∑ d, A c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) z)
          ≤ C * (1 + CA) ^ 2 * (1 + CU) ^ 2 * (1 + KA + U) := by
  classical
  obtain ⟨Cint, hCint0, hCint⟩ := prod_interp_le (ι := ι) (k + 1)
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  refine ⟨N ^ (k - 1) * N ^ 4 * 4 ^ (k - 1) * (Cint + 1) + 1, by positivity, ?_⟩
  intro A u CA CU KA U hAsm hAper husm huper hCA hCU hKA hU hAb hUb hAen hUen
  set w : (ι → ℝ) → ℂ :=
    fun z => ∑ c, ∑ d, A c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) z with hw
  set S : ℝ := CA + CU with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; linarith
  -- the Leibniz expansion, per multi-index
  have hident : ∀ l : Fin (k - 1) → ι,
      Work.Diff.STE.pdVec (k - 1) l w
        = fun z => ∑ b : (ι × ι) × Fin (Work.Diff.STE.splits (List.ofFn l)).length,
            leibTerm A u (List.ofFn l) b z := by
    intro l
    rw [show Work.Diff.STE.pdVec (k - 1) l w = Work.Diff.STE.pdList (List.ofFn l) w from rfl, hw]
    exact pdVec_transport_eq_sum hAsm husm (List.ofFn l)
  -- the per-`l` estimate
  have hstep : ∀ l : Fin (k - 1) → ι,
      ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec (k - 1) l w x‖ ^ 2
        ≤ (N ^ 2 * 2 ^ (k - 1)) * ((N ^ 2 * 2 ^ (k - 1)) * (Cint * (S ^ 2 * (KA + U)))) := by
    intro l
    have hcard : (Fintype.card ((ι × ι) × Fin (Work.Diff.STE.splits (List.ofFn l)).length) : ℝ)
        = N ^ 2 * 2 ^ (k - 1) := by
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
        Work.Diff.STE.cm_splits_length_count, List.length_ofFn, hN]
      push_cast
      ring
    have hterm : ∀ b : (ι × ι) × Fin (Work.Diff.STE.splits (List.ofFn l)).length,
        ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖leibTerm A u (List.ofFn l) b x‖ ^ 2
          ≤ Cint * (S ^ 2 * (KA + U)) := by
      rintro ⟨⟨c, d⟩, i⟩
      set p : List ι × List ι := (Work.Diff.STE.splits (List.ofFn l)).get i with hp
      have hmem : p ∈ Work.Diff.STE.splits (List.ofFn l) := List.get_mem _ i
      have hlen : p.1.length + p.2.length = k - 1 := by
        have h := Work.Diff.STE.cm_splits_mem_length (List.ofFn l) p hmem
        rwa [List.length_ofFn] at h
      have hA : Work.Diff.STE.pdVec p.1.length (fun j => p.1.get j) (A c d)
          = Work.Diff.STE.pdList p.1 (A c d) := pdVec_get_eq_pdList_self p.1 (A c d)
      have hlenB : (p.2 ++ [c, d]).length = p.2.length + 2 := by simp
      have hB : Work.Diff.STE.pdVec (p.2.length + 2)
            (fun j : Fin (p.2.length + 2) => (p.2 ++ [c, d]).get (Fin.cast hlenB.symm j)) u
          = Work.Diff.STE.pdList p.2 (Work.Diff.STE.pd c (Work.Diff.STE.pd d u)) := by
        rw [pdVec_get_eq_pdList_gen hlenB u, Work.Diff.STE.cm_pdList_append]
        rfl
      have hαβ : p.1.length + (p.2.length + 2) = k + 1 := by omega
      have hmain := hCint (A c d) u S KA U (hAsm c d) husm (hAper c d) huper hS0 hKA hU
        (fun z => le_trans (hAb c d z) (le_add_of_nonneg_right hCU))
        (fun z => le_trans (hUb z) (le_add_of_nonneg_left hCA))
        (hAen c d) hUen p.1.length (p.2.length + 2) hαβ
        (fun j => p.1.get j) (fun j => (p.2 ++ [c, d]).get (Fin.cast hlenB.symm j))
      rw [hA, hB] at hmain
      simpa only [hp, leibTerm] using hmain
    calc ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec (k - 1) l w x‖ ^ 2
        = ∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖∑ b : (ι × ι) × Fin (Work.Diff.STE.splits (List.ofFn l)).length,
              leibTerm A u (List.ofFn l) b x‖ ^ 2 := by rw [hident l]
      _ ≤ (Fintype.card ((ι × ι) × Fin (Work.Diff.STE.splits (List.ofFn l)).length) : ℝ)
            * ∑ b : (ι × ι) × Fin (Work.Diff.STE.splits (List.ofFn l)).length,
              ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖leibTerm A u (List.ofFn l) b x‖ ^ 2 :=
          integral_norm_sum_sq_le _ (fun b => continuous_leibTerm hAsm husm _ b)
      _ ≤ (Fintype.card ((ι × ι) × Fin (Work.Diff.STE.splits (List.ofFn l)).length) : ℝ)
            * ∑ _b : (ι × ι) × Fin (Work.Diff.STE.splits (List.ofFn l)).length,
              (Cint * (S ^ 2 * (KA + U))) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => hterm b)) (by positivity)
      _ = (N ^ 2 * 2 ^ (k - 1)) * ((N ^ 2 * 2 ^ (k - 1)) * (Cint * (S ^ 2 * (KA + U)))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  -- the `H^{k-1}` energy is the sum over the multi-indices
  have hEN : Work.Diff.STE.ENormSq (k - 1) w
      = ∑ l : Fin (k - 1) → ι,
          ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec (k - 1) l w x‖ ^ 2 := rfl
  rw [hEN]
  -- arithmetic
  have h2d : (2 : ℝ) ^ (k - 1) * 2 ^ (k - 1) = 4 ^ (k - 1) := by
    rw [← mul_pow]; norm_num
  have hSle : S ≤ (1 + CA) * (1 + CU) := by
    rw [hSdef]
    nlinarith [mul_nonneg hCA hCU]
  have hSsq : S ^ 2 ≤ (1 + CA) ^ 2 * (1 + CU) ^ 2 := by
    have h := pow_le_pow_left₀ hS0 hSle 2
    rwa [mul_pow] at h
  have hmain2 : S ^ 2 * (KA + U) ≤ (1 + CA) ^ 2 * (1 + CU) ^ 2 * (1 + KA + U) :=
    mul_le_mul hSsq (by linarith) (by linarith) (by positivity)
  calc ∑ l : Fin (k - 1) → ι,
        ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec (k - 1) l w x‖ ^ 2
      ≤ ∑ _l : Fin (k - 1) → ι,
          ((N ^ 2 * 2 ^ (k - 1)) * ((N ^ 2 * 2 ^ (k - 1)) * (Cint * (S ^ 2 * (KA + U))))) :=
        Finset.sum_le_sum (fun l _ => hstep l)
    _ = (Fintype.card (Fin (k - 1) → ι) : ℝ)
          * ((N ^ 2 * 2 ^ (k - 1)) * ((N ^ 2 * 2 ^ (k - 1)) * (Cint * (S ^ 2 * (KA + U))))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = N ^ (k - 1) * (N ^ 2 * 2 ^ (k - 1) * (N ^ 2 * 2 ^ (k - 1)
          * (Cint * (S ^ 2 * (KA + U))))) := by
        rw [Fintype.card_fun, Fintype.card_fin, hN]
        push_cast
        ring
    _ = (N ^ (k - 1) * N ^ 4 * 4 ^ (k - 1) * Cint) * (S ^ 2 * (KA + U)) := by
        rw [← h2d]; ring
    _ ≤ (N ^ (k - 1) * N ^ 4 * 4 ^ (k - 1) * (Cint + 1) + 1) * (S ^ 2 * (KA + U)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h1 : (0 : ℝ) ≤ N ^ (k - 1) * N ^ 4 * 4 ^ (k - 1) := by positivity
        nlinarith [hCint0, h1]
    _ ≤ (N ^ (k - 1) * N ^ 4 * 4 ^ (k - 1) * (Cint + 1) + 1)
          * ((1 + CA) ^ 2 * (1 + CU) ^ 2 * (1 + KA + U)) :=
        mul_le_mul_of_nonneg_left hmain2 (by positivity)
    _ = (N ^ (k - 1) * N ^ 4 * 4 ^ (k - 1) * (Cint + 1) + 1)
          * (1 + CA) ^ 2 * (1 + CU) ^ 2 * (1 + KA + U) := by ring

end Work.Diff.STE.Lead.GalTame
