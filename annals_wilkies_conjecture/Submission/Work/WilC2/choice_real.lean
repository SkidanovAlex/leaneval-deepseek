/-
  Area C2 (WilC2): the real side of the definable choice.

  Over `ℝ`, the choice condition `ChoiceCond φ v y` has exactly one solution provided the fibre
  is a finite union of preconnected (i.e. interval) pieces.  The selected point is obtained as
  follows: the leftmost component `LeftComp φ v` of the fibre is a nonempty interval; its image
  `TZset φ v` under the increasing bijection `rescale : ℝ → (-1,1)` is a nonempty bounded
  interval; the midpoint of `[sInf, sSup]` of that interval lies in it (order-convexity), and the
  selected point is the preimage of that midpoint.
-/
import Submission.Work.WilC2.ChoiceDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-! ## 1. Pure order facts about the rescaled component -/

theorem isInfTZ_unique {n : ℕ} {M : Type*} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [LRc.Structure M] {φ : ParamFormula n} {v : Fin n → M} {a b : M}
    (ha : IsInfTZ φ v a) (hb : IsInfTZ φ v b) : a = b :=
  le_antisymm (hb.2 a ha.1) (ha.2 b hb.1)

theorem isSupTZ_unique {n : ℕ} {M : Type*} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [LRc.Structure M] {φ : ParamFormula n} {v : Fin n → M} {a b : M}
    (ha : IsSupTZ φ v a) (hb : IsSupTZ φ v b) : a = b :=
  le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)

theorem isInfTZ_csInf {n : ℕ} (φ : ParamFormula n) (v : Fin n → ℝ)
    (hne : (TZset φ v).Nonempty) (hbd : BddBelow (TZset φ v)) :
    IsInfTZ φ v (sInf (TZset φ v)) :=
  ⟨fun _ ht => csInf_le hbd ht, fun _ h => le_csInf hne h⟩

theorem isSupTZ_csSup {n : ℕ} (φ : ParamFormula n) (v : Fin n → ℝ)
    (hne : (TZset φ v).Nonempty) (hbu : BddAbove (TZset φ v)) :
    IsSupTZ φ v (sSup (TZset φ v)) :=
  ⟨fun _ ht => le_csSup hbu ht, fun _ h => csSup_le hne h⟩

/-! ## 2. Two auxiliary facts (also available as separate lemmas; proved here to keep this file
self-contained) -/

/-- The midpoint of a nonempty bounded interval lies in it. -/
theorem midpoint_mem_ordConnected_aux {I : Set ℝ} (hI : I.OrdConnected) (hne : I.Nonempty)
    (hbdd : BddAbove I) (hbd : BddBelow I) : (sInf I + sSup I) / 2 ∈ I := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hne' : I.Nonempty := ⟨x₀, hx₀⟩
  have hle : sInf I ≤ sSup I := le_trans (csInf_le hbd hx₀) (le_csSup hbdd hx₀)
  rcases eq_or_lt_of_le hle with h | h
  · have hx : x₀ = sInf I :=
      le_antisymm (by rw [h]; exact le_csSup hbdd hx₀) (csInf_le hbd hx₀)
    have : (sInf I + sSup I) / 2 = x₀ := by rw [← h, hx]; ring
    rw [this]; exact hx₀
  · have hτ : ∀ z, sInf I < z → z < sSup I → z ∈ I := by
      intro z hz₁ hz₂
      obtain ⟨p, hpI, hpz⟩ : ∃ p ∈ I, p < z := by
        by_contra hcon
        simp only [not_exists, not_and, not_lt] at hcon
        exact absurd (le_csInf hne' hcon) (not_le.mpr hz₁)
      obtain ⟨q, hqI, hzq⟩ : ∃ q ∈ I, z < q := by
        by_contra hcon
        simp only [not_exists, not_and, not_lt] at hcon
        exact absurd (csSup_le hne' hcon) (not_le.mpr hz₂)
      exact hI.out' hpI hqI ⟨le_of_lt hpz, le_of_lt hzq⟩
    exact hτ _ (by linarith) (by linarith)

/-- The leftmost component of the fibre is nonempty when the fibre is a nonempty finite union of
preconnected pieces. -/
theorem leftComp_nonempty_aux {n : ℕ} (φ : ParamFormula n) {v : Fin n → ℝ}
    {s : Finset (Set ℝ)} (hpre : ∀ I ∈ s, IsPreconnected I)
    (hFib : Fib φ v = ⋃₀ (s : Set (Set ℝ))) (hne : (Fib φ v).Nonempty) :
    (LeftComp φ v).Nonempty := by
  classical
  let s' : Finset (Set ℝ) := s.filter (fun I => I.Nonempty)
  have hs'ne : s'.Nonempty := by
    rcases hne with ⟨x, hx⟩
    obtain ⟨I, hIs, hxI⟩ := Set.mem_sUnion.mp (hFib ▸ hx)
    exact ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hIs, ⟨x, hxI⟩⟩⟩
  let ξ : Set ℝ → ℝ := fun I => if h : I.Nonempty then Classical.choose h else 0
  have hξ : ∀ I ∈ s, I.Nonempty → ξ I ∈ I := by
    intro I _ hI
    simp only [ξ, dif_pos hI]
    exact Classical.choose_spec hI
  obtain ⟨I₀, hI₀s', hI₀min⟩ := Finset.exists_min_image s' ξ hs'ne
  have hI₀s : I₀ ∈ s := (Finset.mem_filter.mp hI₀s').1
  have hI₀ne : I₀.Nonempty := (Finset.mem_filter.mp hI₀s').2
  have hx₁I₀ : ξ I₀ ∈ I₀ := hξ I₀ hI₀s hI₀ne
  have hx₁Fib : ξ I₀ ∈ Fib φ v := by
    rw [hFib]; exact Set.mem_sUnion.mpr ⟨I₀, Finset.mem_coe.mpr hI₀s, hx₁I₀⟩
  refine ⟨ξ I₀, hx₁Fib, ?_⟩
  intro z hzFib hzx w hzw hwx
  obtain ⟨I, hIs, hzI⟩ := Set.mem_sUnion.mp (hFib ▸ hzFib)
  have hIs : I ∈ s := Finset.mem_coe.mp hIs
  have hIs' : I ∈ s' := Finset.mem_filter.mpr ⟨hIs, ⟨z, hzI⟩⟩
  have hle : ξ I₀ ≤ ξ I := hI₀min I hIs'
  have hIord : I.OrdConnected := (hpre I hIs).ordConnected
  have hξI : ξ I ∈ I := hξ I hIs ⟨z, hzI⟩
  have hwI : w ∈ I := hIord.out' hzI hξI
    ⟨le_of_lt hzw, le_of_lt (lt_of_lt_of_le hwx hle)⟩
  rw [hFib]; exact Set.mem_sUnion.mpr ⟨I, Finset.mem_coe.mpr hIs, hwI⟩

/-! ## 3. The real side of the choice -/

/-- **The choice over `ℝ`.**  If every fibre of `φ` is a finite union of preconnected pieces, then
on every nonempty fibre the choice condition has exactly one solution. -/
theorem real_choice {n : ℕ} (φ : ParamFormula n)
    (hfib : ∀ v : Fin n → ℝ, ∃ s : Finset (Set ℝ), (∀ I ∈ s, IsPreconnected I) ∧
      Fib φ v = ⋃₀ (s : Set (Set ℝ))) :
    ∀ v : Fin n → ℝ, (Fib φ v).Nonempty → ∃! y : ℝ, ChoiceCond φ v y := by
  intro v hne
  obtain ⟨s, hpre, hs⟩ := hfib v
  have hZne : (LeftComp φ v).Nonempty := leftComp_nonempty_aux φ hpre hs hne
  have hZord : (LeftComp φ v).OrdConnected := LeftComp_ordConnected
  have hTZeq : TZset φ v = rescale '' LeftComp φ v := TZset_eq_image φ v
  have hTZne : (TZset φ v).Nonempty := by rw [hTZeq]; exact hZne.image rescale
  have hTZbd : BddBelow (TZset φ v) := by rw [hTZeq]; exact rescale_bddBelow _
  have hTZbu : BddAbove (TZset φ v) := by rw [hTZeq]; exact rescale_bddAbove _
  have hTZord : (TZset φ v).OrdConnected := by
    rw [hTZeq]; exact rescale_image_ordConnected hZord
  have hmid : (sInf (TZset φ v) + sSup (TZset φ v)) / 2 ∈ TZset φ v :=
    midpoint_mem_ordConnected_aux hTZord hTZne hTZbu hTZbd
  obtain ⟨y₀, hy₀Z, hy₀rel⟩ := hmid
  refine ⟨y₀, ?_, ?_⟩
  · refine ⟨hy₀Z, sInf (TZset φ v), sSup (TZset φ v),
      (sInf (TZset φ v) + sSup (TZset φ v)) / 2, ?_, ?_, ?_, ?_⟩
    · exact isInfTZ_csInf φ v hTZne hTZbd
    · exact isSupTZ_csSup φ v hTZne hTZbu
    · exact hy₀rel
    · ring
  · intro y hy
    obtain ⟨hyZ, m', s', t, hm', hs', hrel, hsum⟩ := hy
    have hm : m' = sInf (TZset φ v) := isInfTZ_unique hm' (isInfTZ_csInf φ v hTZne hTZbd)
    have hs_ : s' = sSup (TZset φ v) := isSupTZ_unique hs' (isSupTZ_csSup φ v hTZne hTZbu)
    rw [hm, hs_] at hsum
    have ht : t = (sInf (TZset φ v) + sSup (TZset φ v)) / 2 := by linarith
    have h1 : rescale y = t := rescaleRel_iff_real.mp hrel
    have h2 : rescale y₀ = (sInf (TZset φ v) + sSup (TZset φ v)) / 2 :=
      rescaleRel_iff_real.mp hy₀rel
    exact rescale_injective (by rw [h1, ht, ← h2])

end Work.WilC2
