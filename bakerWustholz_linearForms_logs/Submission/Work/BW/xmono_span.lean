import Mathlib
import Submission.Work.BW.finrank_subIdeal_false_defs
import Submission.Work.BW.span_mono
import Submission.Work.BW.eval_mono_eq_of_rowLat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-- The classes of the monomials `xmono d M c` (one per class `c` of the torus box `∏ᵢ [0, d_{i+1}]` modulo `𝒵 = rowLat M`) span the quotient `homPiece N d ⧸ subPiece N ρ d M`. Use `span_mono` for `homPiece N d`, push through the surjective `Submodule.mkQ (subPiece N ρ d M)`, and for each monomial `mono N d b` with `bᵢ ≤ dᵢ`: if `b 0 = 0` it is congruent mod `subPiece` to `xmono d M c` for the class `c` of `torPart b` (`eval_mono_eq_of_rowLat`, `subIdeal_mem_iff_false`); if `b 0 ≥ 1` it lies in `subPiece` (`mono_mem_subIdeal_of_pos`). -/
theorem xmono_span {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ) :
    ⊤ ≤ Submodule.span ℂ (Set.range (fun c : clsSet d M =>
      (Submodule.mkQ (subPiece N ρ d M)) (xmono d M c))) := by
  classical
  -- It suffices to hit every element of the quotient, using surjectivity of `mkQ`.
  rw [top_le_iff, Submodule.eq_top_iff']
  intro x
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective (subPiece N ρ d M) x
  -- The target submodule of the quotient.
  set T : Submodule ℂ (homPiece N d ⧸ subPiece N ρ d M) :=
    Submodule.span ℂ (Set.range (fun c : clsSet d M =>
      (Submodule.mkQ (subPiece N ρ d M)) (xmono d M c))) with hTdef
  -- The monomials `mono N d b` (`b i ≤ d i`), viewed inside `homPiece N d`, span it.
  have hspanTop : Submodule.span ℂ (Set.range (fun b : {b : Fin (N + 1) → ℕ // ∀ i, b i ≤ d i} =>
      (⟨mono N d b.1, mono_mem_homPiece N d b.1 b.2⟩ : homPiece N d))) = ⊤ := by
    have hset : (⇑(homPiece N d).subtype '' Set.range (fun b : {b : Fin (N + 1) → ℕ // ∀ i, b i ≤ d i} =>
        (⟨mono N d b.1, mono_mem_homPiece N d b.1 b.2⟩ : homPiece N d)))
        = Set.range (fun b : {b : Fin (N + 1) → ℕ // ∀ i, b i ≤ d i} => mono N d b.1) := by
      ext y
      constructor
      · rintro ⟨z, ⟨b, rfl⟩, rfl⟩
        exact ⟨b, rfl⟩
      · rintro ⟨b, rfl⟩
        exact ⟨_, ⟨b, rfl⟩, rfl⟩
    have hmap : Submodule.map (homPiece N d).subtype
        (Submodule.span ℂ (Set.range (fun b : {b : Fin (N + 1) → ℕ // ∀ i, b i ≤ d i} =>
          (⟨mono N d b.1, mono_mem_homPiece N d b.1 b.2⟩ : homPiece N d)))) = homPiece N d := by
      rw [Submodule.map_span, hset, ← span_mono N d]
    have hinj : Function.Injective (Submodule.map (homPiece N d).subtype) :=
      Submodule.map_injective_of_injective (Submodule.subtype_injective _)
    rw [← hinj.eq_iff]
    rw [hmap, Submodule.map_subtype_top]
  -- Classification of a single monomial according to its `X_{0,1}`-exponent `b 0`.
  have hkey : ∀ (b : Fin (N + 1) → ℕ) (hb : ∀ i, b i ≤ d i),
      (Submodule.mkQ (subPiece N ρ d M))
        (⟨mono N d b, mono_mem_homPiece N d b hb⟩ : homPiece N d) ∈ T := by
    intro b hb
    by_cases hb0 : b 0 = 0
    · -- `b 0 = 0`: the monomial is congruent mod `subIdeal` to the chosen `xmono` of its class.
      have hmem : torPart b ∈ boxPts N (mBox d) := by
        rw [boxPts_eq_Icc, Finset.mem_Icc]
        constructor
        · intro i; exact Int.natCast_nonneg _
        · intro i
          have h := hb i.succ
          have h' : (b i.succ : ℤ) ≤ (d i.succ : ℤ) := by exact_mod_cast h
          simpa [torPart, mBox] using h'
      let c : clsSet d M := ⟨clsOf N ρ M (torPart b), Finset.mem_image.mpr ⟨torPart b, hmem, rfl⟩⟩
      have hc : (c : (Fin N → ℤ) ⧸ rowLat N ρ M) = clsOf N ρ M (torPart b) := rfl
      -- The chosen representative `repPt d M c` of the class of `torPart b` differs from `torPart b`
      -- by an element of the row lattice.
      have hrep : (Submodule.Quotient.mk (p := rowLat N ρ M) (repPt d M c))
          = (Submodule.Quotient.mk (p := rowLat N ρ M) (torPart b)) := by
        rw [repPt_cls, hc, clsOf]
      have hdiff : repPt d M c - torPart b ∈ rowLat N ρ M :=
        (Submodule.Quotient.eq (rowLat N ρ M)).mp hrep
      have hd0 : repExp d M c 0 = b 0 := by rw [repExp_zero]; omega
      have hcl : ((fun i : Fin N => (repExp d M c i.succ : ℤ)) - (fun i : Fin N => (b i.succ : ℤ)))
          ∈ rowLat N ρ M := by
        show torPart (repExp d M c) - torPart b ∈ rowLat N ρ M
        rw [torPart_repExp]
        exact hdiff
      -- Hence the two monomials agree on `G'`, so their difference lies in the vanishing ideal.
      have hmemI : mono N d (repExp d M c) - mono N d b ∈ subIdeal N ρ false M := by
        rw [subIdeal_mem_iff_false M (Submodule.sub_mem _
          (mono_mem_homPiece N d _ (repExp_le d M c)) (mono_mem_homPiece N d b hb))]
        intro y hy
        rw [map_sub, eval_mono_eq_of_rowLat M d (repExp d M c) b hd0 hcl y hy.2.1 hy.2.2, sub_self]
      have hsub : (⟨mono N d b, mono_mem_homPiece N d b hb⟩ : homPiece N d) - (xmono d M c)
          ∈ subPiece N ρ d M := by
        show ((mono N d b : MR N) - mono N d (repExp d M c)) ∈ subIdeal N ρ false M
        have h2 := neg_mem hmemI
        rwa [neg_sub] at h2
      have hmk : (Submodule.mkQ (subPiece N ρ d M))
            (⟨mono N d b, mono_mem_homPiece N d b hb⟩ : homPiece N d)
          = (Submodule.mkQ (subPiece N ρ d M)) (xmono d M c) := by
        rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero _).mpr hsub
      rw [hmk]
      exact Submodule.subset_span ⟨c, rfl⟩
    · -- `b 0 ≥ 1`: the monomial vanishes on `G'`, so it maps to zero in the quotient.
      have hbpos : 1 ≤ b 0 := by omega
      have hmemb : mono N d b ∈ subIdeal N ρ false M := mono_mem_subIdeal_of_pos d M b hb hbpos
      have hsub : (⟨mono N d b, mono_mem_homPiece N d b hb⟩ : homPiece N d) ∈ subPiece N ρ d M := hmemb
      have hz : (Submodule.mkQ (subPiece N ρ d M))
          (⟨mono N d b, mono_mem_homPiece N d b hb⟩ : homPiece N d) = 0 := by
        rw [Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero _).mpr hsub
      rw [hz]
      exact T.zero_mem
  have hle : Submodule.span ℂ (Set.range (fun b : {b : Fin (N + 1) → ℕ // ∀ i, b i ≤ d i} =>
      (⟨mono N d b.1, mono_mem_homPiece N d b.1 b.2⟩ : homPiece N d))) ≤
      Submodule.comap (Submodule.mkQ (subPiece N ρ d M)) T := by
    rw [Submodule.span_le]
    rintro y ⟨b, rfl⟩
    exact hkey b.1 b.2
  exact hle (by rw [hspanTop]; trivial)

end Work.BW
