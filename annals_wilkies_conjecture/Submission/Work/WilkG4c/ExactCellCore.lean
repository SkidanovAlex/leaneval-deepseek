import Mathlib
import Submission.Work.WilkG4c.ExactCellDefs
import Submission.Work.WilkG4c.exists_mem_image_ivt
import Submission.Work.WilkG4c.strictMonoOn_or_strictAntiOn_of_injOn

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-- **The core facts of the per-cell construction.**  Given the fibre-end data of `κ` over `l`
(the dichotomy `hdich`), the sharp bounds `α l, β l` of the image of the fibre under `f`, the
inverse data `g` of `f` along the fibre, and the expansion estimate `hexp` of `f` along the
fibre, we obtain all the facts the chart construction uses. -/
theorem exactCell_core {p : ℕ} {κ : Set (Fin (p + 1) → ℝ)} {f : (Fin (p + 1) → ℝ) → ℝ}
    {g : (Fin (p + 1) → ℝ) → ℝ} {α β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ}
    (hcube : κ ⊆ Work.WilG4c.inCubeSet p 1)
    (hval : ∀ w ∈ κ, f w ∈ Set.Ioo (0 : ℝ) 1)
    (hexp : ∀ w ∈ κ, ∀ w' ∈ κ, Fin.init w = Fin.init w' →
      |w (Fin.last p) - w' (Fin.last p)| ≤ |f w - f w'|)
    (hcontf : ∀ x : ℝ, Fin.snoc l x ∈ κ → ContinuousAt (fun s : ℝ => f (Fin.snoc l s)) x)
    (hKord : ({s : ℝ | Fin.snoc l s ∈ κ}).OrdConnected)
    (hdich : (∃ c : ℝ, {s : ℝ | Fin.snoc l s ∈ κ} = {c}) ∨
      (∃ A B : ℝ, A < B ∧ {s : ℝ | Fin.snoc l s ∈ κ} = Set.Ioo A B))
    (hαβprop : (∀ η : ℝ, Fin.snoc l η ∈ imgSet κ f → α l ≤ η ∧ η ≤ β l) ∧
      (∀ u : ℝ, α l < u → ∃ x : ℝ, Fin.snoc l x ∈ imgSet κ f ∧ x < u) ∧
      (∀ u : ℝ, u < β l → ∃ x : ℝ, Fin.snoc l x ∈ imgSet κ f ∧ u < x))
    (hglo : ∀ u : Fin (p + 1) → ℝ, (∃ x : ℝ, Fin.snoc u x ∈ invSet κ f) →
      (∀ x : ℝ, Fin.snoc u x ∈ invSet κ f → g u ≤ x) ∧
      (∀ v : ℝ, g u < v → ∃ x : ℝ, Fin.snoc u x ∈ invSet κ f ∧ x < v))
    (hlne : ∃ s : ℝ, Fin.snoc l s ∈ κ) :
    CellFacts κ f g α β l := by
  let K : Set ℝ := {s : ℝ | Fin.snoc l s ∈ κ}
  let fl : ℝ → ℝ := fun s => f (Fin.snoc l s)
  have hfl : ∀ s : ℝ, fl s = f (Fin.snoc l s) := fun s => rfl
  have hexpK : ∀ x ∈ K, ∀ y ∈ K, |x - y| ≤ |fl x - fl y| := by
    intro x hx y hy
    have h := hexp (Fin.snoc l x) hx (Fin.snoc l y) hy (by rw [Fin.init_snoc, Fin.init_snoc])
    rw [Fin.snoc_last, Fin.snoc_last] at h
    exact h
  have hcont_fl : ∀ x ∈ K, ContinuousAt fl x := fun x hx => hcontf x hx
  have hinj_fl : Set.InjOn fl K := by
    intro x hx y hy hxy
    have h := hexpK x hx y hy
    rw [hxy, sub_self, abs_zero] at h
    have h' : |x - y| = 0 := le_antisymm h (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp h')
  -- ### the image fibre
  have hmem_img : ∃ η : ℝ, Fin.snoc l η ∈ imgSet κ f := by
    obtain ⟨s, hs⟩ := hlne
    exact ⟨f (Fin.snoc l s), (mem_imgSet).mpr ⟨s, hs, rfl⟩⟩
  obtain ⟨hbound, hsharpα, hsharpβ⟩ := hαβprop
  obtain ⟨η₀, hη₀m⟩ := hmem_img
  have hαβle : α l ≤ β l := le_trans (hbound η₀ hη₀m).1 (hbound η₀ hη₀m).2
  have hboundfl : ∀ s : ℝ, Fin.snoc l s ∈ κ → α l ≤ fl s ∧ fl s ≤ β l := by
    intro s hs
    exact hbound (f (Fin.snoc l s)) ((mem_imgSet).mpr ⟨s, hs, rfl⟩)
  have hIVT : ∀ η : ℝ, α l < η → η < β l → ∃ s : ℝ, Fin.snoc l s ∈ κ ∧ fl s = η := by
    intro η h1 h2
    have h := exists_mem_image_ivt (K := K) (f := fl) hKord hcont_fl
      (fun u hu => by
        obtain ⟨η', hη'1, hη'2⟩ := hsharpα u hu
        obtain ⟨s, hs1, hs2⟩ := (mem_imgSet).mp hη'1
        exact ⟨s, hs1, by rw [hfl s, hs2]; exact hη'2⟩)
      (fun u hu => by
        obtain ⟨η', hη'1, hη'2⟩ := hsharpβ u hu
        obtain ⟨s, hs1, hs2⟩ := (mem_imgSet).mp hη'1
        exact ⟨s, hs1, by rw [hfl s, hs2]; exact hη'2⟩)
      η h1 h2
    exact h
  -- ### the fibre of `κ` is an open interval in the non-degenerate case
  have hKint : α l < β l → ∃ A B : ℝ, A < B ∧ K = Set.Ioo A B := by
    intro hlt
    rcases hdich with ⟨c, hc3⟩ | ⟨A, B, hAB, hK⟩
    · exfalso
      have hcK : Fin.snoc l c ∈ κ := by
        have hmem : c ∈ ({s : ℝ | Fin.snoc l s ∈ κ}) := by
          rw [hc3]
          exact Set.mem_singleton c
        exact hmem
      have hvimg : Fin.snoc l (f (Fin.snoc l c)) ∈ imgSet κ f :=
        (mem_imgSet).mpr ⟨c, hcK, rfl⟩
      have hall : ∀ η : ℝ, Fin.snoc l η ∈ imgSet κ f → η = f (Fin.snoc l c) := by
        intro η hη
        obtain ⟨s, hs1, hs2⟩ := (mem_imgSet).mp hη
        have hsc : s = c := by
          have hmem : s ∈ ({c} : Set ℝ) := by
            rw [← hc3]
            exact hs1
          exact Set.mem_singleton_iff.mp hmem
        rw [hsc] at hs2
        exact hs2.symm
      have hαeq : α l = f (Fin.snoc l c) := by
        refine le_antisymm (hbound _ hvimg).1 ?_
        by_contra hcon
        have hlt' : α l < f (Fin.snoc l c) := lt_of_not_ge hcon
        obtain ⟨η', hη'1, hη'2⟩ := hsharpα _ hlt'
        exact absurd (hall η' hη'1) (ne_of_lt hη'2)
      have hβeq : β l = f (Fin.snoc l c) := by
        refine le_antisymm ?_ (hbound _ hvimg).2
        by_contra hcon
        have hlt' : f (Fin.snoc l c) < β l := lt_of_not_ge hcon
        obtain ⟨η', hη'1, hη'2⟩ := hsharpβ _ hlt'
        exact absurd (hall η' hη'1) (ne_of_gt hη'2)
      exact absurd (hαeq.trans hβeq.symm) (ne_of_lt hlt)
    · exact ⟨A, B, hAB, hK⟩
  have hstrict : α l < β l → ∀ x ∈ K, α l < fl x ∧ fl x < β l := by
    intro hlt x hxK
    obtain ⟨A, B, hAB, hKAB⟩ := hKint hlt
    have hxAB : x ∈ Set.Ioo A B := by rw [← hKAB]; exact hxK
    obtain ⟨sm, hsm1, hsm2⟩ := exists_between hxAB.1
    obtain ⟨sp, hsp1, hsp2⟩ := exists_between hxAB.2
    have hsmK : sm ∈ K := by rw [hKAB]; exact ⟨hsm1, lt_trans hsm2 hxAB.2⟩
    have hspK : sp ∈ K := by rw [hKAB]; exact ⟨lt_trans hxAB.1 hsp1, hsp2⟩
    rcases strictMonoOn_or_strictAntiOn_of_injOn hKord hcont_fl hinj_fl with hmono | hanti
    · have h1 : fl sm < fl x := hmono hsmK hxK hsm2
      have h2 : fl x < fl sp := hmono hxK hspK hsp1
      exact ⟨lt_of_le_of_lt (hboundfl sm hsmK).1 h1, lt_of_lt_of_le h2 (hboundfl sp hspK).2⟩
    · have h1 : fl x < fl sm := hanti hsmK hxK hsm2
      have h2 : fl sp < fl x := hanti hxK hspK hsp1
      exact ⟨lt_of_le_of_lt (hboundfl sp hspK).1 h2, lt_of_lt_of_le h1 (hboundfl sm hsmK).2⟩
  -- ### `g` is the inverse of `fl`
  have hsingle : ∀ η s s' : ℝ,
      (Fin.snoc (Fin.snoc l η : Fin (p + 1) → ℝ) s : Fin (p + 2) → ℝ) ∈ invSet κ f →
      (Fin.snoc (Fin.snoc l η : Fin (p + 1) → ℝ) s' : Fin (p + 2) → ℝ) ∈ invSet κ f →
      s = s' := by
    intro η s s' hs hs'
    rw [mem_invSet] at hs hs'
    have h1 : f (Fin.snoc l s) = f (Fin.snoc l s') := by rw [hs.2, hs'.2]
    have h2 : |f (Fin.snoc l s) - f (Fin.snoc l s')| = 0 := by rw [h1, sub_self, abs_zero]
    have h3 := hexp (Fin.snoc l s) hs.1 (Fin.snoc l s') hs'.1
      (by rw [Fin.init_snoc, Fin.init_snoc])
    rw [Fin.snoc_last, Fin.snoc_last, h2] at h3
    have h4 : |s - s'| = 0 := le_antisymm h3 (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp h4)
  have hgeq : ∀ η s : ℝ,
      (Fin.snoc (Fin.snoc l η : Fin (p + 1) → ℝ) s : Fin (p + 2) → ℝ) ∈ invSet κ f →
      g (Fin.snoc l η) = s := by
    intro η s hs
    obtain ⟨hg1, hg2⟩ := hglo (Fin.snoc l η) ⟨s, hs⟩
    have hle := hg1 s hs
    by_contra hne
    have hlt : g (Fin.snoc l η) < s := lt_of_le_of_ne hle hne
    obtain ⟨x, hx, hxu⟩ := hg2 ((g (Fin.snoc l η) + s) / 2) (by linarith)
    have hxs : x = s := hsingle η x s hx hs
    rw [hxs] at hxu
    linarith
  have hηimg : ∀ τ ∈ Set.Ioo (0 : ℝ) 1,
      ∃ s : ℝ, Fin.snoc l s ∈ κ ∧ fl s = α l + τ * (β l - α l) := by
    intro τ hτ
    by_cases hlt : α l < β l
    · obtain ⟨s, hs1, hs2⟩ := hIVT (α l + τ * (β l - α l))
        (by nlinarith [hτ.1, hτ.2, sub_pos.mpr hlt])
        (by nlinarith [hτ.1, hτ.2, sub_pos.mpr hlt])
      exact ⟨s, hs1, hs2⟩
    · have heq : α l = β l := le_antisymm hαβle (le_of_not_gt hlt)
      have hzero : α l + τ * (β l - α l) = α l := by rw [heq]; ring
      rw [hzero]
      have hαmem : Fin.snoc l (α l) ∈ imgSet κ f := by
        have hη'α : η₀ = α l :=
          le_antisymm (by rw [heq]; exact (hbound η₀ hη₀m).2) (hbound η₀ hη₀m).1
        simpa [← hη'α] using hη₀m
      obtain ⟨s, hs1, hs2⟩ := (mem_imgSet).mp hαmem
      exact ⟨s, hs1, hs2⟩
  -- ### bounds on the ends
  have hβ1 : β l ≤ 1 := by
    by_contra hcon
    have hlt' : 1 < β l := lt_of_not_ge hcon
    obtain ⟨η', hη'1, hη'2⟩ := hsharpβ 1 hlt'
    obtain ⟨s', hs'1, hs'2⟩ := (mem_imgSet).mp hη'1
    have hv := hval (Fin.snoc l s') hs'1
    rw [hs'2] at hv
    linarith [hv.2]
  have hα0 : 0 ≤ α l := by
    by_contra hcon
    have hlt' : α l < 0 := lt_of_not_ge hcon
    obtain ⟨η', hη'1, hη'2⟩ := hsharpα 0 hlt'
    obtain ⟨s', hs'1, hs'2⟩ := (mem_imgSet).mp hη'1
    have hv := hval (Fin.snoc l s') hs'1
    rw [hs'2] at hv
    linarith [hv.1]
  refine ⟨hαβle, hα0, hβ1, hboundfl, ?_, hIVT, hgeq, hηimg, hstrict, hKint⟩
  intro x y hx hy hxy
  exact hinj_fl hx hy hxy

end Work.WilkG4c
