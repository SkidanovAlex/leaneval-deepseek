import Mathlib

namespace Work.TMC14Core

namespace RootSignAux

open Polynomial

/-- A multiset product of complex numbers with zero imaginary part is real. -/
lemma multiset_prod_of_im_zero (t : Multiset ℂ) (h : ∀ z ∈ t, z.im = 0) :
    t.prod = ((t.map Complex.re).prod : ℂ) := by
  revert h
  refine Multiset.induction_on t ?_ ?_
  · intro _
    rw [Multiset.map_zero, Multiset.prod_zero, Multiset.prod_zero, Complex.ofReal_one]
  · intro a s ih h
    have ha : a.im = 0 := h a (Multiset.mem_cons_self a s)
    have hs : ∀ z ∈ s, z.im = 0 := fun z hz => h z (Multiset.mem_cons_of_mem hz)
    have haz : a = (a.re : ℂ) := by
      apply Complex.ext <;> simp [ha]
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, ih hs]
    conv_lhs => rw [haz]
    rw [← Complex.ofReal_mul]

/-- A multiset sum of complex numbers with zero imaginary part is real. -/
lemma multiset_sum_of_im_zero (t : Multiset ℂ) (h : ∀ z ∈ t, z.im = 0) :
    t.sum = ((t.map Complex.re).sum : ℂ) := by
  revert h
  refine Multiset.induction_on t ?_ ?_
  · intro _
    rw [Multiset.map_zero, Multiset.sum_zero, Multiset.sum_zero, Complex.ofReal_zero]
  · intro a s ih h
    have ha : a.im = 0 := h a (Multiset.mem_cons_self a s)
    have hs : ∀ z ∈ s, z.im = 0 := fun z hz => h z (Multiset.mem_cons_of_mem hz)
    have haz : a = (a.re : ℂ) := by
      apply Complex.ext <;> simp [ha]
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, ih hs]
    conv_lhs => rw [haz]
    rw [← Complex.ofReal_add]

/-- `∏ z∈t (0 - z)` is a real number, whose real part is `∏ z∈t (-z.re)`. -/
lemma prod_zero_sub_re (t : Multiset ℂ) (h : ∀ z ∈ t, z.im = 0) :
    ((t.map (fun z => (0:ℂ) - z)).prod).im = 0 ∧
      ((t.map (fun z => (0:ℂ) - z)).prod).re = (t.map (fun z => -z.re)).prod := by
  have hmap : ∀ z ∈ t.map (fun z => (0:ℂ) - z), z.im = 0 := by
    intro z hz
    rw [Multiset.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simp [h w hw]
  have h1 := multiset_prod_of_im_zero _ hmap
  constructor
  · rw [h1, Complex.ofReal_im]
  · rw [h1, Complex.ofReal_re]
    apply congrArg Multiset.prod
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro z hz
    simp

/-- `∏ z∈t (-z.re) = (-1)^{card t} · ∏ z∈t z.re`. -/
lemma prod_neg_re (t : Multiset ℂ) :
    (t.map (fun z => -z.re)).prod = (-1:ℝ)^(t.card) * (t.map Complex.re).prod := by
  have h1 : t.map (fun z => -z.re) = (t.map Complex.re).map (fun x => -x) := by
    rw [Multiset.map_map]; rfl
  rw [h1, Multiset.prod_map_neg, Multiset.card_map]

/-- A nonempty multiset of positive reals has positive sum. -/
lemma multiset_sum_pos {s : Multiset ℝ} (h : ∀ a ∈ s, 0 < a) (hs : s ≠ 0) :
    0 < s.sum := by
  have key : ∀ u : Multiset ℝ, u ≠ 0 → (∀ a ∈ u, 0 < a) → 0 < u.sum := by
    intro u
    refine Multiset.induction_on u ?_ ?_
    · intro hu _
      exact absurd rfl hu
    · intro a t ih ht hh
      rw [Multiset.sum_cons]
      rcases eq_or_ne t 0 with ht0 | ht0
      · rw [ht0, Multiset.sum_zero, add_zero]
        exact hh a (Multiset.mem_cons_self a t)
      · have htsum : 0 < t.sum := ih ht0 (fun z hz => hh z (Multiset.mem_cons_of_mem hz))
        have ha : 0 < a := hh a (Multiset.mem_cons_self a t)
        linarith
  exact key s hs h

lemma neg_one_pow_mul_pred (n : ℕ) (hn : n ≠ 0) :
    (-1:ℝ)^n * (-1:ℝ)^(n-1) = -1 := by
  rw [← pow_add]
  have hodd : Odd (n + (n - 1)) := ⟨n - 1, by omega⟩
  rw [hodd.neg_one_pow]

end RootSignAux

open Polynomial

theorem rootSignPositiveRoots (q : Polynomial ℂ) (hmonic : q.Monic) (hdeg : q.natDegree ≠ 0)
    (h0 : q.eval 0 ≠ 0) (hpos : ∀ z ∈ q.roots, z.im = 0 ∧ 0 < z.re) :
    (q.eval 0).im = 0 ∧ (q.derivative.eval 0).im = 0 ∧
      (q.eval 0).re * (q.derivative.eval 0).re < 0 := by
  have hsp : q.Splits := IsAlgClosed.splits q
  have him : ∀ z ∈ q.roots, z.im = 0 := fun z hz => (hpos z hz).1
  have hrepos : ∀ z ∈ q.roots, 0 < z.re := fun z hz => (hpos z hz).2
  have hcard : q.roots.card ≠ 0 := by
    rw [← hsp.natDegree_eq_card_roots]
    exact hdeg
  have heval : q.eval 0 = (q.roots.map (fun z => (0:ℂ) - z)).prod :=
    hsp.eval_eq_prod_roots_of_monic hmonic 0
  have hderiv : q.derivative.eval 0 =
      (q.roots.map (fun a => ((q.roots.erase a).map (fun z => (0:ℂ) - z)).prod)).sum := by
    rw [hsp.eval_derivative 0, Monic.leadingCoeff hmonic, one_mul]
  have him_eval : (q.eval 0).im = 0 := by
    rw [heval]
    exact (RootSignAux.prod_zero_sub_re q.roots him).1
  have hre_eval : (q.eval 0).re = (-1:ℝ)^(q.roots.card) * (q.roots.map Complex.re).prod := by
    rw [heval, (RootSignAux.prod_zero_sub_re q.roots him).2, RootSignAux.prod_neg_re]
  have h1 : (q.roots.map (fun a => ((q.roots.erase a).map (fun z => (0:ℂ) - z)).prod)).sum =
      (↑(q.roots.map (fun a => ((q.roots.erase a).map (fun z => (-z.re : ℝ))).prod)).sum : ℂ) := by
    rw [RootSignAux.multiset_sum_of_im_zero _ (by
      intro z hz
      rw [Multiset.mem_map] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      exact (RootSignAux.prod_zero_sub_re (q.roots.erase a)
        (fun z hz => him z (Multiset.mem_of_mem_erase hz))).1)]
    refine congrArg Complex.ofReal ?_
    have hm : (q.roots.map (fun a => ((q.roots.erase a).map (fun z => (0:ℂ) - z)).prod)).map Complex.re
        = q.roots.map (fun a => ((q.roots.erase a).map (fun z => (-z.re : ℝ))).prod) := by
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro a ha
      exact (RootSignAux.prod_zero_sub_re (q.roots.erase a)
        (fun z hz => him z (Multiset.mem_of_mem_erase hz))).2
    rw [hm]
  have h2 : (q.roots.map (fun a => ((q.roots.erase a).map (fun z => (-z.re : ℝ))).prod)).sum =
      (-1:ℝ)^(q.roots.card - 1) *
        (q.roots.map (fun a => ((q.roots.erase a).map Complex.re).prod)).sum := by
    have hmap : q.roots.map (fun a => ((q.roots.erase a).map (fun z => (-z.re : ℝ))).prod) =
        q.roots.map (fun a => (-1:ℝ)^(q.roots.card - 1) *
          ((q.roots.erase a).map Complex.re).prod) := by
      apply Multiset.map_congr rfl
      intro a ha
      show ((q.roots.erase a).map (fun z => (-z.re : ℝ))).prod =
        (-1:ℝ)^(q.roots.card - 1) * ((q.roots.erase a).map Complex.re).prod
      rw [RootSignAux.prod_neg_re]
      have hcard' : (q.roots.erase a).card = q.roots.card - 1 := by
        have := Multiset.card_erase_add_one ha
        omega
      rw [hcard']
    rw [hmap, Multiset.sum_map_mul_left]
  have him_deriv : (q.derivative.eval 0).im = 0 := by
    rw [hderiv, h1, Complex.ofReal_im]
  have hre_deriv : (q.derivative.eval 0).re =
      (-1:ℝ)^(q.roots.card - 1) *
        (q.roots.map (fun a => ((q.roots.erase a).map Complex.re).prod)).sum := by
    rw [hderiv, h1, Complex.ofReal_re, h2]
  have hApos : 0 < (q.roots.map Complex.re).prod := by
    apply Multiset.prod_pos
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact hrepos z hz
  have hBpos : 0 < (q.roots.map (fun a => ((q.roots.erase a).map Complex.re).prod)).sum := by
    apply RootSignAux.multiset_sum_pos
    · intro a ha
      rw [Multiset.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      apply Multiset.prod_pos
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact hrepos z (Multiset.mem_of_mem_erase hz)
    · intro hzero
      apply hcard
      have hh : (q.roots.map (fun a => ((q.roots.erase a).map Complex.re).prod)).card = 0 := by
        rw [hzero, Multiset.card_zero]
      rwa [Multiset.card_map] at hh
  refine ⟨him_eval, him_deriv, ?_⟩
  have hprod : ((-1:ℝ)^(q.roots.card) * (q.roots.map Complex.re).prod) *
      ((-1:ℝ)^(q.roots.card - 1) *
        (q.roots.map (fun a => ((q.roots.erase a).map Complex.re).prod)).sum) =
      -((q.roots.map Complex.re).prod *
        (q.roots.map (fun a => ((q.roots.erase a).map Complex.re).prod)).sum) := by
    rw [mul_mul_mul_comm, RootSignAux.neg_one_pow_mul_pred q.roots.card hcard, neg_one_mul]
  rw [hre_eval, hre_deriv, hprod]
  have hAB : 0 < (q.roots.map Complex.re).prod *
      (q.roots.map (fun a => ((q.roots.erase a).map Complex.re).prod)).sum :=
    mul_pos hApos hBpos
  linarith

end Work.TMC14Core
