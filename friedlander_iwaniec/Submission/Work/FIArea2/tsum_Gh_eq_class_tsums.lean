import Mathlib
import Submission.Work.FIArea2.CCountPoissonDefs
import Submission.Work.FIArea2.Adm_iff_dvd

namespace Work.FIArea2

open Finset
open scoped BigOperators

noncomputable section

/-! ## Auxiliary facts about the Euclidean class/quotient maps `qVec`/`cVec` -/

/-- For a residue vector `γ ∈ [0,m)²`, the Euclidean class of the coset point `cosetVec m γ c` is
`γ` again. -/
lemma qVec_cosetVec {m : ℕ} (_hm : 0 < m) {γ : ℕ × ℕ}
    (hγ : γ ∈ Finset.range m ×ˢ Finset.range m) (c : ℤ × ℤ) :
    qVec m (cosetVec m γ c) = γ := by
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hγ
  rw [Finset.mem_range] at h1 h2
  ext
  · simp only [qVec, cosetVec]
    have hmod : ((γ.1 : ℤ) + (m : ℤ) * c.1) % (m : ℤ) = (γ.1 : ℤ) := by
      rw [Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by positivity) (by exact_mod_cast h1)]
    rw [hmod, Int.toNat_natCast]
  · simp only [qVec, cosetVec]
    have hmod : ((γ.2 : ℤ) + (m : ℤ) * c.2) % (m : ℤ) = (γ.2 : ℤ) := by
      rw [Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by positivity) (by exact_mod_cast h2)]
    rw [hmod, Int.toNat_natCast]

/-- For a residue vector `γ ∈ [0,m)²`, the Euclidean quotient of the coset point `cosetVec m γ c`
is `c` again. -/
lemma cVec_cosetVec {m : ℕ} (hm : 0 < m) {γ : ℕ × ℕ}
    (hγ : γ ∈ Finset.range m ×ˢ Finset.range m) (c : ℤ × ℤ) :
    cVec m (cosetVec m γ c) = c := by
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hγ
  rw [Finset.mem_range] at h1 h2
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  ext
  · simp only [cVec, cosetVec]
    rw [Int.add_mul_ediv_left (γ.1 : ℤ) c.1 hmZ,
      Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast h1)]
    ring
  · simp only [cVec, cosetVec]
    rw [Int.add_mul_ediv_left (γ.2 : ℤ) c.2 hmZ,
      Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast h2)]
    ring

/-! ## The decomposition of a finitely supported sum over `ℤ²` into the cosets of `mℤ²` -/

/-- **Decomposition into cosets modulo `m`.**  A function `f : ℤ² → ℂ` whose support is contained
in a finite set `S` can be summed either over all of `ℤ²` or over the finitely many cosets
`γ + mℤ²`, `γ ∈ [0,m)²`, each summed over `ℤ²`; the two agree.  This is the reindexing behind
the identity `∑_p Gh(p) = ∑_{γ} ∑_c Gh(γ + mc)` of the Poisson step (6.9). -/
lemma tsum_eq_coset_sum {m : ℕ} (hm : 0 < m) (f : ℤ × ℤ → ℂ) (S : Finset (ℤ × ℤ))
    (hS : ∀ p, f p ≠ 0 → p ∈ S) :
    (∑' p, f p) =
      ∑ γ ∈ Finset.range m ×ˢ Finset.range m,
        ∑ c ∈ S.image (cVec m), f (cosetVec m γ c) := by
  classical
  have hL : (∑' p, f p) = ∑ p ∈ S.filter (fun p => f p ≠ 0), f p := by
    refine tsum_eq_sum' (s := S.filter (fun p => f p ≠ 0)) ?_
    intro p hp
    exact Finset.mem_filter.mpr ⟨hS p hp, hp⟩
  have hbij :
      (∑ p ∈ S.filter (fun p => f p ≠ 0), f p)
        = ∑ x ∈ ((Finset.range m ×ˢ Finset.range m) ×ˢ (S.image (cVec m))).filter
            (fun x => f (cosetVec m x.1 x.2) ≠ 0),
          f (cosetVec m x.1 x.2) := by
    refine Finset.sum_bij (fun p _ => (qVec m p, cVec m p)) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hpS, hpf⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨qVec_mem hm p, ?_⟩, ?_⟩
      · exact Finset.mem_image.mpr ⟨p, hpS, rfl⟩
      · rwa [cosetVec_qVec_cVec hm p]
    · intro p1 _ p2 _ heq
      have h1 : cosetVec m (qVec m p1) (cVec m p1)
          = cosetVec m (qVec m p2) (cVec m p2) := by
        rw [Prod.mk.injEq] at heq
        rw [heq.1, heq.2]
      rwa [cosetVec_qVec_cVec hm p1, cosetVec_qVec_cVec hm p2] at h1
    · intro b hb
      obtain ⟨hb', hbf⟩ := Finset.mem_filter.mp hb
      obtain ⟨hbG, _⟩ := Finset.mem_product.mp hb'
      refine ⟨cosetVec m b.1 b.2, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hS _ hbf, hbf⟩
      · show (qVec m (cosetVec m b.1 b.2), cVec m (cosetVec m b.1 b.2)) = b
        rw [qVec_cosetVec hm hbG b.2, cVec_cosetVec hm hbG b.2]
    · intro p _
      show f p = f (cosetVec m (qVec m p) (cVec m p))
      rw [cosetVec_qVec_cVec hm p]
  have hdrop :
      (∑ x ∈ ((Finset.range m ×ˢ Finset.range m) ×ˢ (S.image (cVec m))).filter
            (fun x => f (cosetVec m x.1 x.2) ≠ 0), f (cosetVec m x.1 x.2))
        = ∑ x ∈ (Finset.range m ×ˢ Finset.range m) ×ˢ (S.image (cVec m)),
            f (cosetVec m x.1 x.2) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x hx hxt
    by_contra h
    exact hxt (Finset.mem_filter.mpr ⟨hx, h⟩)
  have hprod :
      (∑ x ∈ (Finset.range m ×ˢ Finset.range m) ×ˢ (S.image (cVec m)),
            f (cosetVec m x.1 x.2))
        = ∑ γ ∈ Finset.range m ×ˢ Finset.range m,
            ∑ c ∈ S.image (cVec m), f (cosetVec m γ c) := by
    rw [Finset.sum_product]
  rw [hL, hbij, hdrop, hprod]

/-! ## The target identity -/

theorem tsum_Gh_eq_class_tsums (Pa : Work.FITop.Params) (F : ℝ → ℝ) (z1 z2 : GaussianInt)
    (hm : Work.FIPlan.absDelta z1 z2 ≠ 0)
    (hsupp : ∀ p : ℤ × ℤ, Work.FIArea2.Adm z1 z2 p →
      Work.FIArea2.PsiC F z1 z2 ((p.1 : ℝ), (p.2 : ℝ)) ≠ 0 →
      p ∈ Work.FIArea2.Kbox Pa z1 z2) :
    (∑' p : ℤ × ℤ, Work.FIArea2.Gh F z1 z2 p)
      = ∑ γ ∈ Finset.range (Work.FIPlan.absDelta z1 z2)
            ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2),
          ∑' c : ℤ × ℤ, Work.FIArea2.Gh F z1 z2
            (Work.FIArea2.cosetVec (Work.FIPlan.absDelta z1 z2) γ c) := by
  classical
  have hm0 : 0 < Work.FIPlan.absDelta z1 z2 := Nat.pos_of_ne_zero hm
  have hS : ∀ p : ℤ × ℤ,
      Work.FIArea2.Gh F z1 z2 p ≠ 0 → p ∈ Work.FIArea2.Kbox Pa z1 z2 := by
    intro p hp
    rw [Work.FIArea2.Gh] at hp
    split_ifs at hp with hAdm
    · exact hsupp p hAdm hp
    · exact absurd rfl hp
  have hkey := tsum_eq_coset_sum (m := Work.FIPlan.absDelta z1 z2) hm0
      (Work.FIArea2.Gh F z1 z2) (Work.FIArea2.Kbox Pa z1 z2) hS
  rw [hkey]
  refine Finset.sum_congr rfl ?_
  intro γ hγ
  refine (tsum_eq_sum'
    (s := (Work.FIArea2.Kbox Pa z1 z2).image (cVec (Work.FIPlan.absDelta z1 z2))) ?_).symm
  intro c hc
  have hmem : Work.FIArea2.cosetVec (Work.FIPlan.absDelta z1 z2) γ c
      ∈ Work.FIArea2.Kbox Pa z1 z2 := hS _ hc
  have hcc : cVec (Work.FIPlan.absDelta z1 z2)
        (Work.FIArea2.cosetVec (Work.FIPlan.absDelta z1 z2) γ c)
      ∈ (Work.FIArea2.Kbox Pa z1 z2).image (cVec (Work.FIPlan.absDelta z1 z2)) :=
    Finset.mem_image.mpr ⟨_, hmem, rfl⟩
  rwa [cVec_cosetVec hm0 hγ c] at hcc

end

end Work.FIArea2
