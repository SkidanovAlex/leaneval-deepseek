import Mathlib
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_degree_zero_finrank
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_ideal_degree_le
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_quotient_map_equiv

namespace Commons.Algebra.FreeAlgebra

open _root_.FreeAlgebra

set_option linter.unusedTactic false in
noncomputable def freeMonoidWordsEquivVector (ι : Type*) (d : ℕ) :
    {w : FreeMonoid ι // (FreeMonoid.toList w).length = d} ≃ List.Vector ι d where
  toFun w := ⟨FreeMonoid.toList w.1, w.2⟩
  invFun v := ⟨FreeMonoid.ofList v.1, by
    change (FreeMonoid.toList (FreeMonoid.ofList v.1)).length = d
    rw [FreeMonoid.toList_ofList]
    exact v.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    change FreeMonoid.ofList (FreeMonoid.toList w.1) = w.1
    exact FreeMonoid.ofList_toList w.1
  right_inv := by
    intro v
    apply Subtype.ext
    change FreeMonoid.toList (FreeMonoid.ofList v.1) = v.1
    rw [FreeMonoid.toList_ofList]

lemma golodShafarevich_words_finite (ι : Type*) [Fintype ι] (d : ℕ) :
    Finite {w : FreeMonoid ι // (FreeMonoid.toList w).length = d} := by
  let e := freeMonoidWordsEquivVector ι d
  have hvec : Finite (List.Vector ι d) := inferInstance
  exact Finite.of_equiv (List.Vector ι d) e.symm

lemma golodShafarevich_gradedPart_finiteDimensional {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (d : ℕ) :
    Module.Finite K (golodShafarevich_gradedPart K ι d) := by
  classical
  let W := {w : FreeMonoid ι // (FreeMonoid.toList w).length = d}
  have hW : Finite W := golodShafarevich_words_finite ι d
  let s : Set (FreeAlgebra K ι) :=
    {x | ∃ w : FreeMonoid ι,
      (FreeMonoid.toList w).length = d ∧ x = FreeAlgebra.basisFreeMonoid K ι w}
  have hs : s.Finite := by
    have hrange : (Set.range (fun w : W => FreeAlgebra.basisFreeMonoid K ι w.1)).Finite :=
      Set.finite_range _
    refine hrange.subset ?_
    intro x hx
    rcases hx with ⟨w, hlen, rfl⟩
    exact ⟨⟨w, hlen⟩, rfl⟩
  change Module.Finite K (Submodule.span K s)
  exact Module.Finite.span_of_finite K hs

lemma golodShafarevich_twoSidedIdeal_mul_basisFreeMonoid_mem
    {K ι σ : Type*} [Field K]
    (rel : σ → FreeAlgebra K ι) {a : FreeAlgebra K ι}
    (ha : a ∈ golodShafarevich_twoSidedIdeal K ι σ rel) (u : FreeMonoid ι) :
    a * FreeAlgebra.basisFreeMonoid K ι u ∈ golodShafarevich_twoSidedIdeal K ι σ rel := by
  let I := golodShafarevich_twoSidedIdeal K ι σ rel
  refine Submodule.span_induction
    (p := fun x (_ : x ∈ I) => x * FreeAlgebra.basisFreeMonoid K ι u ∈ I) ?_ ?_ ?_ ?_ ha
  · intro x hx
    rcases hx with ⟨s, v, w, rfl⟩
    have hEq :
        (FreeAlgebra.basisFreeMonoid K ι v * rel s * FreeAlgebra.basisFreeMonoid K ι w) *
          FreeAlgebra.basisFreeMonoid K ι u =
          FreeAlgebra.basisFreeMonoid K ι v * rel s *
            FreeAlgebra.basisFreeMonoid K ι (w * u) := by
      rw [mul_assoc, golodShafarevich_basisFreeMonoid_mul]
    rw [hEq]
    apply Submodule.subset_span
    exact ⟨s, v, w * u, rfl⟩
  · simp
  · intro x y hx hy ihx ihy
    rw [add_mul]
    exact Submodule.add_mem _ ihx ihy
  · intro c x hx ihx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c ihx

lemma golodShafarevich_relator_mul_mem_T
    {K ι σ : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (degRel : σ → ℕ) (rel : σ → FreeAlgebra K ι)
    (hdeg : ∀ r, 2 ≤ degRel r)
    (hhom : ∀ r, rel r ∈ golodShafarevich_gradedPart K ι (degRel r))
    (n : ℕ) (hn : 0 < n) (r : σ) (hr : degRel r ≤ n)
    {a : FreeAlgebra K ι}
    (haI : a ∈ golodShafarevich_twoSidedIdeal K ι σ rel)
    (haW : a ∈ golodShafarevich_gradedPart K ι (n - degRel r)) :
    a * rel r ∈ Submodule.span K {x | ∃ a ∈ golodShafarevich_twoSidedIdeal K ι σ rel ⊓
      golodShafarevich_gradedPart K ι (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)} := by
  let V := golodShafarevich_gradedPart K ι
  let I := golodShafarevich_twoSidedIdeal K ι σ rel
  let T := Submodule.span K {x | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
  let d := degRel r
  have hd2 : 2 ≤ d := by simpa [d] using hdeg r
  have hdn : d ≤ n := by simpa [d] using hr
  have haI' : a ∈ I := by simpa [I] using haI
  have haW' : a ∈ V (n - d) := by simpa [V, d] using haW
  change a * rel r ∈ T
  refine Submodule.span_induction
    (p := fun y (_ : y ∈ V d) => a * y ∈ T) ?_ ?_ ?_ ?_
    (by simpa [golodShafarevich_gradedPart, V, d] using (hhom r))
  · intro y hy
    rcases hy with ⟨w, hlen, rfl⟩
    have hwlen : FreeMonoid.length w = d := by simpa [FreeMonoid.length] using hlen
    have hw1 : w ≠ 1 := by
      intro hw
      have hwlen0 : FreeMonoid.length w = 0 := by simp [hw]
      omega
    rcases golodShafarevich_freeMonoid_exists_mul_of_of_ne_one hw1 with ⟨u, i, hwfac⟩
    have hlenu : FreeMonoid.length u = d - 1 := by
      have hwlen_mul : FreeMonoid.length w = FreeMonoid.length u + 1 := by
        rw [hwfac, FreeMonoid.length_mul, FreeMonoid.length_of]
      omega
    have hbasis_w : FreeAlgebra.basisFreeMonoid K ι w =
        FreeAlgebra.basisFreeMonoid K ι u * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i) := by
      rw [hwfac]
      exact golodShafarevich_basisFreeMonoid_mul u (FreeMonoid.of i)
    have haI_mul : a * FreeAlgebra.basisFreeMonoid K ι u ∈ I :=
      golodShafarevich_twoSidedIdeal_mul_basisFreeMonoid_mem (rel := rel) haI' u
    have hprod_deg : a * FreeAlgebra.basisFreeMonoid K ι u ∈ V ((n - d) + (d - 1)) := by
      have hbasis_mem := golodShafarevich_basisFreeMonoid_mem_gradedPart (K := K) (ι := ι) u
      have hprod := golodShafarevich_gradedPart_mul_mem (K := K) (ι := ι) haW' hbasis_mem
      simpa [hlenu] using hprod
    have hdeg_sum : (n - d) + (d - 1) = n - 1 := by omega
    have haV : a * FreeAlgebra.basisFreeMonoid K ι u ∈ V (n - 1) := by
      simpa [hdeg_sum] using hprod_deg
    have haInt : a * FreeAlgebra.basisFreeMonoid K ι u ∈ I ⊓ V (n - 1) := ⟨haI_mul, haV⟩
    have hstep :
        a * FreeAlgebra.basisFreeMonoid K ι w =
          (a * FreeAlgebra.basisFreeMonoid K ι u) * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i) := by
      rw [hbasis_w, mul_assoc]
    rw [hstep]
    dsimp [T]
    apply Submodule.subset_span
    exact ⟨a * FreeAlgebra.basisFreeMonoid K ι u, haInt, i, rfl⟩
  · simp
  · intro y z hy hz ihy ihz
    rw [mul_add]
    exact Submodule.add_mem _ ihy ihz
  · intro c y hy ihy
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c ihy

set_option linter.style.haveILetI false in
theorem golod_shafarevich_relator_right_mul_finrank_le
    {K ι σ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype σ]
    (degRel : σ → ℕ) (rel : σ → FreeAlgebra K ι)
    (hdeg : ∀ r, 2 ≤ degRel r)
    (hhom : ∀ r, rel r ∈ golodShafarevich_gradedPart K ι (degRel r))
    (n : ℕ) (hn : 0 < n) (r : σ) (hr : degRel r ≤ n) :
    let V := golodShafarevich_gradedPart K ι
    let I := golodShafarevich_twoSidedIdeal K ι σ rel
    let T := Submodule.span K {x | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
    let S := Submodule.span K {x | ∃ a ∈ V (n - degRel r), x = a * rel r}
    Module.finrank K (Submodule.map T.mkQ S) ≤
      Module.finrank K (Submodule.map I.mkQ (V (n - degRel r))) := by
  dsimp only
  let V := golodShafarevich_gradedPart K ι
  let I := golodShafarevich_twoSidedIdeal K ι σ rel
  let T := Submodule.span K {x | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
  let S := Submodule.span K {x | ∃ a ∈ V (n - degRel r), x = a * rel r}
  let d := degRel r
  let W := V (n - d)
  let A : Submodule K W := Submodule.comap W.subtype I
  have hW_fin : Module.Finite K W := by
    dsimp [W]
    exact golodShafarevich_gradedPart_finiteDimensional (K := K) (ι := ι) (n - d)
  haveI : Module.Finite K (W ⧸ A) := by
    exact Module.Finite.quotient K A
  let f0 : W →ₗ[K] FreeAlgebra K ι := (LinearMap.mulRight K (rel r)).domRestrict W
  have hf0_mem : ∀ a : W, f0 a ∈ S := by
    intro a
    dsimp [f0, S]
    apply Submodule.subset_span
    refine ⟨(a : FreeAlgebra K ι), ?_, rfl⟩
    dsimp [W, V, d]
    exact a.2
  let g : W →ₗ[K] (FreeAlgebra K ι ⧸ T) := T.mkQ.comp f0
  have hf0_range : f0.range = S := by
    apply le_antisymm
    · rintro x ⟨a, rfl⟩
      exact hf0_mem a
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with ⟨a, haW, rfl⟩
      exact ⟨⟨a, haW⟩, by simp [f0]⟩
  have hrange : g.range = Submodule.map T.mkQ S := by
    change (T.mkQ.comp f0).range = Submodule.map T.mkQ S
    rw [LinearMap.range_comp, hf0_range]
  let eRange : g.range ≃ₗ[K] Submodule.map T.mkQ S :=
    LinearEquiv.ofEq g.range (Submodule.map T.mkQ S) hrange
  let eTarget : (W ⧸ g.ker) ≃ₗ[K] Submodule.map T.mkQ S :=
    g.quotKerEquivRange.trans eRange
  have hfin_target : Module.finrank K (Submodule.map T.mkQ S) =
      Module.finrank K (W ⧸ g.ker) := by
    exact LinearEquiv.finrank_eq eTarget.symm
  have hker : A ≤ g.ker := by
    intro a haA
    rw [LinearMap.mem_ker]
    have haI : (a : FreeAlgebra K ι) ∈ I := by
      rw [Submodule.mem_comap] at haA
      simpa [A] using haA
    have haW : (a : FreeAlgebra K ι) ∈ V (n - d) := by
      dsimp [W] at a
      exact a.2
    have hmemT : (a : FreeAlgebra K ι) * rel r ∈ T := by
      dsimp [T, V, I, d]
      exact golodShafarevich_relator_mul_mem_T (K := K) (ι := ι) (σ := σ)
        degRel rel hdeg hhom n hn r hr haI haW
    have hg : g a = T.mkQ ((a : FreeAlgebra K ι) * rel r) := by
      simp [g, f0]
    rw [hg]
    change Submodule.Quotient.mk (p := T) ((a : FreeAlgebra K ι) * rel r) = 0
    exact (Submodule.Quotient.mk_eq_zero T).2 hmemT
  have hle_quot : Module.finrank K (W ⧸ g.ker) ≤ Module.finrank K (W ⧸ A) := by
    exact LinearMap.finrank_le_finrank_of_surjective (Submodule.factor_surjective hker)
  have hR_fin : Module.finrank K (Submodule.map I.mkQ W) =
      Module.finrank K (W ⧸ A) := by
    obtain ⟨eR⟩ := golod_shafarevich_quotient_map_equiv (K := K) (ι := ι) I W
    have hA : A = Submodule.comap W.subtype I := rfl
    rw [hA]
    exact LinearEquiv.finrank_eq eR
  have hmain : Module.finrank K (Submodule.map T.mkQ S) ≤
      Module.finrank K (Submodule.map I.mkQ W) := by
    rw [hfin_target]
    exact le_trans hle_quot (by rw [hR_fin])
  simpa [W, d] using hmain

end Commons.Algebra.FreeAlgebra
