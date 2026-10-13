import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG4b.posPoly_mem
import Submission.Work.WilG1.Calc.finite_of_interior_empty

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.WilG1.OneDim

open WilkiesDesign WilkiesConjecture

/-- A subset of `ℝ` which is a finite union of preconnected sets and which accumulates at `x`
from the right contains a whole right-neighbourhood of `x`.

The two ingredients are: (i) some member of the finite union accumulates at `x` (if none did,
a uniform positive `δ` would witness that the union has no point in `(x, x+δ)`, contradicting
the accumulation hypothesis); (ii) a preconnected subset of `ℝ` containing points arbitrarily
close to `x` on the right is order-convex, so it contains `(x, y₀)` as soon as it contains a
point `y₀ > x`. -/
lemma finite_union_preconnected_accumulates (B : Set ℝ) {x : ℝ}
    (hB : ∃ s : Finset (Set ℝ), (∀ c ∈ s, IsPreconnected c) ∧ B = ⋃₀ (s : Set (Set ℝ)))
    (hacc : ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ B ∧ x < y ∧ y < x + δ) :
    ∃ β : ℝ, x < β ∧ Set.Ioo x β ⊆ B := by
  obtain ⟨s, hpre, hBeq⟩ := hB
  -- `s` is nonempty, otherwise `B = ∅` contradicts the accumulation hypothesis.
  have hsne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with h | h
    · exfalso
      obtain ⟨y, hyB, -⟩ := hacc 1 (by norm_num)
      rw [hBeq, h] at hyB
      simp at hyB
    · exact h
  -- Some member of the union accumulates at `x` from the right.
  have hex : ∃ c ∈ s, ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ c ∧ x < y ∧ y < x + δ := by
    by_contra hcon
    push_neg at hcon
    let δc : Set ℝ → ℝ := fun c => if hc : c ∈ s then Classical.choose (hcon c hc) else 1
    have hδc : ∀ c ∈ s, 0 < δc c ∧ ∀ y, y ∈ c → x < y → x + δc c ≤ y := by
      intro c hc
      simp only [δc, dif_pos hc]
      exact Classical.choose_spec (hcon c hc)
    set δ := s.inf' hsne δc with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef, Finset.lt_inf'_iff]
      intro c hc
      exact (hδc c hc).1
    have hδle : ∀ c ∈ s, δ ≤ δc c := by
      intro c hc
      rw [hδdef]
      exact Finset.inf'_le δc hc
    obtain ⟨y, hyB, hxy, hyδ⟩ := hacc δ hδpos
    rw [hBeq] at hyB
    obtain ⟨c, hcs, hyc⟩ := Set.mem_sUnion.mp hyB
    have hle1 : x + δ ≤ x + δc c := by linarith [hδle c hcs]
    have hle2 : x + δc c ≤ y := (hδc c hcs).2 y hyc hxy
    linarith [hyδ, hle1, hle2]
  -- The accumulating piece contains a right-neighbourhood of `x`.
  obtain ⟨c, hcs, hcacc⟩ := hex
  obtain ⟨y₀, hy₀c, hxy₀, -⟩ := hcacc 1 (by norm_num)
  refine ⟨y₀, hxy₀, ?_⟩
  intro z hz
  rw [Set.mem_Ioo] at hz
  obtain ⟨hxz, hzy₀⟩ := hz
  obtain ⟨w, hwc, hxw, hwz⟩ := hcacc (z - x) (by linarith)
  have hwz' : w < z := by linarith
  have hzI : z ∈ Set.Icc w y₀ := ⟨le_of_lt hwz', le_of_lt hzy₀⟩
  have hzc : z ∈ c := (hpre c hcs).Icc_subset hwc hy₀c hzI
  rw [hBeq]
  exact Set.subset_sUnion_of_mem hcs hzc

theorem interval_of_accumulates {S : WilkiesDesign.SOMin} {a d : ℕ} {A : Set (Fin 1 → ℝ)}
    (hA : A ∈ S.Ω a d 1) {x : ℝ}
    (hacc : ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, (fun _ : Fin 1 => y) ∈ A ∧ x < y ∧ y < x + δ) :
    ∃ β : ℝ, x < β ∧ ∀ y : ℝ, x < y → y < β → (fun _ : Fin 1 => y) ∈ A := by
  classical
  -- Decompose `A` into finitely many preconnected pieces (`SOMin.comps`).
  obtain ⟨p, hp⟩ := S.comps a
  obtain ⟨s, _hcard, hpre, hAeq⟩ := hp d A hA
  -- Transport along the homeomorphism `(Fin 1 → ℝ) ≃ₜ ℝ`, evaluation at the unique index.
  let e : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ
  have hBdec : ∃ s' : Finset (Set ℝ), (∀ c ∈ s', IsPreconnected c) ∧
      e '' A = ⋃₀ (s' : Set (Set ℝ)) := by
    refine ⟨s.image (fun c => e '' c), ?_, ?_⟩
    · intro c' hc'
      rw [Finset.mem_image] at hc'
      obtain ⟨c, hc, rfl⟩ := hc'
      exact (hpre c hc).image _ e.continuous.continuousOn
    · rw [Finset.coe_image, ← Set.image_sUnion, hAeq]
  have haccB : ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ e '' A ∧ x < y ∧ y < x + δ := by
    intro δ hδ
    obtain ⟨y, hyA, hxy, hyδ⟩ := hacc δ hδ
    have he : e (fun _ => y) = y := by
      rw [show e = Homeomorph.funUnique (Fin 1) ℝ from rfl, Homeomorph.funUnique_apply]
    exact ⟨y, ⟨fun _ => y, hyA, he⟩, hxy, hyδ⟩
  obtain ⟨β, hxβ, hβsub⟩ := finite_union_preconnected_accumulates (e '' A) hBdec haccB
  refine ⟨β, hxβ, ?_⟩
  intro y hxy hyβ
  have hyB : y ∈ e '' A := hβsub (by rw [Set.mem_Ioo]; exact ⟨hxy, hyβ⟩)
  obtain ⟨f, hfA, hfe⟩ := hyB
  -- `e` is evaluation at the unique index, so `f = fun _ => y`.
  have hfy : f = fun _ : Fin 1 => y := by
    funext i
    have h0 : f default = y :=
      (congr_fun (Homeomorph.funUnique_apply (Fin 1) ℝ) f).symm.trans hfe
    rw [Subsingleton.elim i default]
    exact h0
  rw [hfy] at hfA
  exact hfA

end Work.WilG1.OneDim
