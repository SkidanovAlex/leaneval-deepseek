import Mathlib
import Submission.Work.OddBound.polygonValue.balancing.Defs
import Submission.Work.OddBound.polygonValue.balancing.exists_strictMono_enum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.polygonValue

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

/-- Composition of a `C¹` function on `[0,1]` with an affine reparametrisation whose values on
the interval stay in `[0,1]`. -/
lemma contMDiffOn_comp_affine_div
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f : ℝ → M} {ℓ c L α β : ℝ}
    (hf : ContMDiffOn 𝓘(ℝ) I 1 f (Set.Icc (0:ℝ) 1))
    (hmem : ∀ s ∈ Set.Icc α β, (ℓ * s - c) / L ∈ Set.Icc (0:ℝ) 1) :
    ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => f ((ℓ * s - c) / L)) (Set.Icc α β) := by
  have hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ) 1 (fun s : ℝ => (ℓ * s - c) / L) :=
    (((contMDiff_const (c := ℓ)).mul contMDiff_id).sub (contMDiff_const (c := c))).div_const L
  have hcomp := ContMDiffOn.comp hf hg.contMDiffOn (fun s hs => hmem s hs)
  simpa only [Function.comp_def] using hcomp

/-- **The arclength-parametrised broken geodesic of a slice is piecewise `C¹`.**

Hypotheses: `hK` identifies `gPt τ ·` on each side interval `[cumLen τ i, cumLen τ (i+1)]` with the
side curve `S i · τ` (affinely reparametrised by arclength) and `hSsm` says the side curves are `C¹`
in the side parameter.  Then there is a strictly increasing finite partition
`0 = a 0 < a 1 < ⋯ < a k = 1` of `[0,1]` — namely the *distinct* breakpoints
`cumLen τ j / totLen τ`, `j ≤ N` (and `0, 1` in the degenerate case `totLen τ = 0`) — such that
`s ↦ gPt τ (totLen τ * s)` is `C¹` on each piece.

Proof plan: write `ℓ := totLen τ`.  For `ℓ = 0` the composite is constant (`gPt τ 0`), so `k = 1`,
`a 0 = 0`, `a 1 = 1` works.  For `ℓ > 0`, let `A` be the finite set of images of the breakpoints
`cumLen τ j / ℓ` (`j = 0, …, N`); it contains `0` and `1` and lies in `[0,1]`.  Let `a` be the
increasing enumeration of `A` (e.g. `A.orderEmbOfFin` for the cardinality, or the existing
`Work.OddBound.polygonValue.balancing.exists_strictMono_enum`); then `a` is `StrictMono` with
`a 0 = 0`, `a (Fin.last k) = 1`.  For a piece `[a j, a (j+1)]` the interval contains no breakpoint in
its interior, so it is contained in some side interval `[cumLen τ m/ℓ, cumLen τ (m+1)/ℓ]` with
`sideLen τ m > 0`; by `hK` the composite there equals
`s ↦ S m ((ℓ * s - cumLen τ m)/sideLen τ m) τ`, an affine reparametrisation of `S m · τ` whose
parameter stays in `[0,1]`, hence is `C¹` (`ContMDiffOn.comp` with `hSsm m`, and `ContMDiffOn.congr`
to transfer to the composite). -/
theorem exists_partition_gPt_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {p : M} {N : ℕ} (hN : 0 < N) {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) 1)
    (hSsm : ∀ i : Fin N, ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0:ℝ) 1))
    (hK : ∀ i : Fin N, ∀ y ∈ Set.Icc (cumLen (I := I) p w τ (i : ℕ)) (cumLen (I := I) p w τ ((i : ℕ) + 1)),
      gPt (I := I) p hN w S τ y = S i ((y - cumLen (I := I) p w τ (i : ℕ)) / sideLen (I := I) p w τ (i : ℕ)) τ) :
    ∃ (k : ℕ) (a : Fin (k + 1) → ℝ),
      StrictMono a ∧ a 0 = 0 ∧ a (Fin.last k) = 1 ∧
      ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1
        (fun s : ℝ => gPt (I := I) p hN w S τ (totLen (I := I) p w τ * s))
        (Set.Icc (a j.castSucc) (a j.succ)) := by
  classical
  have hℓnn : 0 ≤ totLen (I := I) p w τ := totLen_nonneg (I := I) p w τ
  have hcum0 : cumLen (I := I) p w τ 0 = 0 := cumLen_zero (I := I) p w τ
  have hcumN : cumLen (I := I) p w τ N = totLen (I := I) p w τ :=
    (totLen_eq_cumLen (I := I) p w τ).symm
  rcases eq_or_lt_of_le hℓnn with hℓ | hℓ
  · -- degenerate case: the slice has length zero, so the composite curve is constant
    refine ⟨1, fun i : Fin (1 + 1) => (((i : ℕ) : ℝ)), ?_, ?_, ?_, ?_⟩
    · intro i j hij
      show ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ)
      have h : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp hij
      exact_mod_cast h
    · simp
    · simp
    · intro j
      refine ContMDiffOn.congr (contMDiffOn_const (c := gPt (I := I) p hN w S τ 0)) (fun s _ => ?_)
      show gPt (I := I) p hN w S τ (totLen (I := I) p w τ * s)
        = gPt (I := I) p hN w S τ 0
      rw [← hℓ, zero_mul]
  · -- main case: `0 < totLen τ`
    set A : Finset ℝ := (Finset.range (N + 1)).image
        (fun j : ℕ => cumLen (I := I) p w τ j / totLen (I := I) p w τ) with hAdef
    have hA0 : (0 : ℝ) ∈ A := by
      rw [hAdef]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp [hcum0]⟩
    have hA1 : (1 : ℝ) ∈ A := by
      rw [hAdef]
      refine Finset.mem_image.mpr ⟨N, Finset.mem_range.mpr (by omega), ?_⟩
      show cumLen (I := I) p w τ N / totLen (I := I) p w τ = 1
      rw [hcumN, div_self (ne_of_gt hℓ)]
    have hAsub : ∀ x ∈ A, x ∈ Set.Icc (0:ℝ) 1 := by
      intro x hx
      rw [hAdef] at hx
      obtain ⟨j, hj, hxj⟩ := Finset.mem_image.mp hx
      have hjN : j ≤ N := by
        have := Finset.mem_range.mp hj
        omega
      have hcj : cumLen (I := I) p w τ j ≤ totLen (I := I) p w τ := by
        rw [← hcumN]
        exact cumLen_mono (I := I) p w τ hjN
      subst hxj
      constructor
      · exact div_nonneg (cumLen_nonneg (I := I) p w τ j) (le_of_lt hℓ)
      · rw [div_le_iff₀ hℓ]
        simpa using hcj
    obtain ⟨k, a, hmono_a, ha0, ha1, hrange⟩ :=
      balancing.exists_strictMono_enum hA0 hA1 hAsub
    refine ⟨k, a, hmono_a, ha0, ha1, ?_⟩
    have hmemA : ∀ i : Fin (k + 1), a i ∈ A := by
      intro i
      have h : a i ∈ Set.range a := Set.mem_range.mpr ⟨i, rfl⟩
      rw [hrange] at h
      exact Finset.mem_coe.mp h
    -- every element of `A` lying in a closed piece is one of its endpoints
    have hend : ∀ (j : Fin k) (x : ℝ), x ∈ A → a j.castSucc ≤ x → x ≤ a j.succ →
        x = a j.castSucc ∨ x = a j.succ := by
      intro j x hxA hle hge
      have hxA' : x ∈ (A : Set ℝ) := Finset.mem_coe.mpr hxA
      rw [← hrange] at hxA'
      obtain ⟨i, hi⟩ := Set.mem_range.mp hxA'
      subst hi
      rcases lt_or_ge i j.succ with hlt | hge'
      · left
        have hle' : i ≤ j.castSucc := by
          rw [Fin.le_def, Fin.val_castSucc]
          have hlt' := Fin.lt_def.mp hlt
          rw [Fin.val_succ] at hlt'
          omega
        exact le_antisymm (hmono_a.monotone hle') hle
      · right
        exact le_antisymm hge (hmono_a.monotone hge')
    intro j
    have hαβ : a j.castSucc < a j.succ := hmono_a (Fin.castSucc_lt_succ (i := j))
    have hαA : a j.castSucc ∈ A := hmemA j.castSucc
    have hβA : a j.succ ∈ A := hmemA j.succ
    have hα0 : 0 ≤ a j.castSucc := (hAsub _ hαA).1
    have hβ1 : a j.succ ≤ 1 := (hAsub _ hβA).2
    have hβpos : 0 < a j.succ := lt_of_le_of_lt hα0 hαβ
    -- `m₁` is the first breakpoint at or beyond `totLen τ * a (j+1)`
    set T : Finset ℕ := (Finset.range (N + 1)).filter
        (fun i => totLen (I := I) p w τ * a j.succ ≤ cumLen (I := I) p w τ i) with hTdef
    have hTne : T.Nonempty := by
      refine ⟨N, ?_⟩
      rw [hTdef, Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
      rw [hcumN]
      calc totLen (I := I) p w τ * a j.succ ≤ totLen (I := I) p w τ * 1 :=
            mul_le_mul_of_nonneg_left hβ1 (le_of_lt hℓ)
        _ = totLen (I := I) p w τ := mul_one _
    set m₁ : ℕ := T.min' hTne with hm₁def
    have hm₁mem : m₁ ∈ T := Finset.min'_mem T hTne
    have hm₁min : ∀ i ∈ T, m₁ ≤ i := fun i hi => Finset.min'_le T i hi
    have hm₁leN : m₁ ≤ N := by
      have h := hm₁mem
      rw [hTdef, Finset.mem_filter] at h
      have := Finset.mem_range.mp h.1
      omega
    have hyβ : totLen (I := I) p w τ * a j.succ ≤ cumLen (I := I) p w τ m₁ := by
      have h := hm₁mem
      rw [hTdef, Finset.mem_filter] at h
      exact h.2
    have hm₁pos : 0 < m₁ := by
      by_contra hcon
      have hzero : m₁ = 0 := by omega
      rw [hzero, hcum0] at hyβ
      have hpos : 0 < totLen (I := I) p w τ * a j.succ := mul_pos hℓ hβpos
      linarith
    set m : ℕ := m₁ - 1 with hmdef
    have hmval : m + 1 = m₁ := by omega
    have hmltN : m < N := by omega
    have hmrange : m ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hcum_m1_ge : totLen (I := I) p w τ * a j.succ ≤ cumLen (I := I) p w τ (m + 1) := by
      rw [hmval]
      exact hyβ
    have hcum_m_lt : cumLen (I := I) p w τ m < totLen (I := I) p w τ * a j.succ := by
      by_contra hcon
      have hcon' : totLen (I := I) p w τ * a j.succ ≤ cumLen (I := I) p w τ m := not_lt.mp hcon
      have hmem : m ∈ T := by
        rw [hTdef, Finset.mem_filter]
        exact ⟨hmrange, hcon'⟩
      have hle := hm₁min m hmem
      omega
    have hcum_m_le_α : cumLen (I := I) p w τ m ≤ totLen (I := I) p w τ * a j.castSucc := by
      by_contra hcon
      have hcon' : totLen (I := I) p w τ * a j.castSucc < cumLen (I := I) p w τ m :=
        not_le.mp hcon
      have hxA : cumLen (I := I) p w τ m / totLen (I := I) p w τ ∈ A := by
        rw [hAdef]
        exact Finset.mem_image.mpr ⟨m, hmrange, rfl⟩
      have hltβ : cumLen (I := I) p w τ m / totLen (I := I) p w τ < a j.succ := by
        rw [div_lt_iff₀ hℓ]
        nlinarith [hcum_m_lt]
      have hgtα : a j.castSucc < cumLen (I := I) p w τ m / totLen (I := I) p w τ := by
        rw [lt_div_iff₀ hℓ]
        nlinarith [hcon']
      rcases hend j _ hxA (le_of_lt hgtα) (le_of_lt hltβ) with h | h
      · exact absurd h.symm (ne_of_lt hgtα)
      · exact absurd h (ne_of_lt hltβ)
    have hslpos : 0 < sideLen (I := I) p w τ m := by
      have h3 : totLen (I := I) p w τ * a j.castSucc < totLen (I := I) p w τ * a j.succ :=
        mul_lt_mul_of_pos_left hαβ hℓ
      rw [sideLen_eq_sub]
      linarith
    have hGmem : ∀ s ∈ Set.Icc (a j.castSucc) (a j.succ),
        (totLen (I := I) p w τ * s - cumLen (I := I) p w τ m) / sideLen (I := I) p w τ m
          ∈ Set.Icc (0:ℝ) 1 := by
      intro s hs
      rw [Set.mem_Icc] at hs ⊢
      have hts : totLen (I := I) p w τ * a j.castSucc ≤ totLen (I := I) p w τ * s :=
        mul_le_mul_of_nonneg_left hs.1 (le_of_lt hℓ)
      have hts' : totLen (I := I) p w τ * s ≤ totLen (I := I) p w τ * a j.succ :=
        mul_le_mul_of_nonneg_left hs.2 (le_of_lt hℓ)
      constructor
      · exact div_nonneg (by linarith) (le_of_lt hslpos)
      · rw [div_le_one hslpos, sideLen_eq_sub]
        linarith
    have hKapply : ∀ s ∈ Set.Icc (a j.castSucc) (a j.succ),
        gPt (I := I) p hN w S τ (totLen (I := I) p w τ * s)
          = S ⟨m, hmltN⟩ ((totLen (I := I) p w τ * s - cumLen (I := I) p w τ m)
              / sideLen (I := I) p w τ m) τ := by
      intro s hs
      rw [Set.mem_Icc] at hs
      have hts : totLen (I := I) p w τ * a j.castSucc ≤ totLen (I := I) p w τ * s :=
        mul_le_mul_of_nonneg_left hs.1 (le_of_lt hℓ)
      have hts' : totLen (I := I) p w τ * s ≤ totLen (I := I) p w τ * a j.succ :=
        mul_le_mul_of_nonneg_left hs.2 (le_of_lt hℓ)
      have hy : totLen (I := I) p w τ * s ∈
          Set.Icc (cumLen (I := I) p w τ ((⟨m, hmltN⟩ : Fin N) : ℕ))
            (cumLen (I := I) p w τ (((⟨m, hmltN⟩ : Fin N) : ℕ) + 1)) := by
        rw [Set.mem_Icc]
        exact ⟨le_trans hcum_m_le_α hts, le_trans hts' hcum_m1_ge⟩
      have h := hK ⟨m, hmltN⟩ (totLen (I := I) p w τ * s) hy
      simpa only [Fin.val_mk] using h
    refine ContMDiffOn.congr
      (contMDiffOn_comp_affine_div (f := fun r : ℝ => S ⟨m, hmltN⟩ r τ)
        (ℓ := totLen (I := I) p w τ) (c := cumLen (I := I) p w τ m)
        (L := sideLen (I := I) p w τ m) (α := a j.castSucc) (β := a j.succ)
        (hSsm ⟨m, hmltN⟩) hGmem)
      (fun s hs => hKapply s hs)

end Work.OddBound.polygonValue
