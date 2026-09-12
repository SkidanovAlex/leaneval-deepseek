import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Submission.Commons.Lattice.Discrete.discreteTopology_span_linIndep

noncomputable section
open scoped BigOperators
open Submodule Module

namespace Commons.Lattice.Discrete

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The real dimension of the ℝ-span of a discrete ℤ-submodule equals its ℤ-rank. -/
lemma finrank_span_eq_finrank (n : ℕ) (ℒ : Submodule ℤ (E n)) [DiscreteTopology ℒ] :
    Module.finrank ℝ (span ℝ (ℒ : Set (E n))) = Module.finrank ℤ ℒ := by
  have hdisc : DiscreteTopology (span ℤ (ℒ : Set (E n))) := by
    rw [Submodule.span_eq]
    infer_instance
  have hEq := Real.finrank_eq_int_finrank_of_discrete (E := E n) (s := (ℒ : Set (E n))) hdisc
  change Module.finrank ℝ (span ℝ (ℒ : Set (E n))) = Module.finrank ℤ (span ℤ (ℒ : Set (E n))) at hEq
  rw [Submodule.span_eq] at hEq
  exact hEq

/-- The ambient values of a ℤ-basis of a discrete submodule are ℝ-linearly independent. -/
lemma linearIndependent_ambient_basis (n : ℕ) (ℒ : Submodule ℤ (E n)) [DiscreteTopology ℒ]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ ℒ) :
    LinearIndependent ℝ (fun i : ι => (b i : E n)) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  unfold Set.finrank
  have hspan : span ℝ (Set.range (fun i : ι => (b i : E n))) = span ℝ (ℒ : Set (E n)) := by
    have hZ : span ℤ (Set.range (fun i : ι => (b i : E n))) = ℒ := by
      have h1 : span ℤ (Set.range (fun i : ι => (b i : E n))) = Submodule.map (Submodule.subtype ℒ) ⊤ := by
        calc
          span ℤ (Set.range (fun i : ι => (b i : E n))) = Submodule.map (Submodule.subtype ℒ) (span ℤ (Set.range b)) := by
            rw [Submodule.map_span]
            congr
            ext x; simp
          _ = Submodule.map (Submodule.subtype ℒ) ⊤ := by rw [b.span_eq]
      rw [h1]
      simp
    calc
      span ℝ (Set.range (fun i : ι => (b i : E n))) = span ℝ ((span ℤ (Set.range (fun i : ι => (b i : E n)))) : Set (E n)) := by
        rw [Submodule.span_span_of_tower ℤ ℝ]
      _ = span ℝ (ℒ : Set (E n)) := by rw [hZ]
  rw [hspan]
  rw [finrank_span_eq_finrank n ℒ]
  exact (Module.finrank_eq_card_basis b).symm

/-- Orthogonal projection onto `Sᗮ` kills elements of `S`. -/
lemma proj_orth_eq_zero_of_mem (n : ℕ) (S : Submodule ℝ (E n)) {x : E n} (hx : x ∈ S) :
    (Submodule.orthogonal S).starProjection x = 0 := by
  have hx' : x ∈ Sᗮᗮ := by
    rw [Submodule.orthogonal_orthogonal S]
    exact hx
  have hkill : ∀ {U : Submodule ℝ (E n)} {y : E n}, y ∈ Uᗮ → U.starProjection y = 0 := by
    intro U y hy
    simpa using (Submodule.eq_starProjection_of_mem_orthogonal (K := U) (u := y) (v := 0)
      (Submodule.zero_mem U) (by simpa using hy))
  exact hkill (U := Submodule.orthogonal S) hx'

/-- If orthogonal projection onto `Sᗮ` kills `x`, then `x ∈ S`. -/
lemma mem_of_proj_orth_eq_zero (n : ℕ) (S : Submodule ℝ (E n)) {x : E n}
    (hx : (Submodule.orthogonal S).starProjection x = 0) : x ∈ S := by
  have hdec : x = S.starProjection x + (Submodule.orthogonal S).starProjection x := by
    have h : (Submodule.orthogonal S).starProjection x = x - S.starProjection x := by
      rw [Submodule.starProjection_orthogonal' S]
      rfl
    rw [h]
    abel
  rw [hdec, hx, add_zero]
  exact Submodule.starProjection_apply_mem S x

/- Quotient-lattice discreteness: for discrete Z-lattices `ℒ' ⊆ ℒ` in E = EuclideanSpace ℝ
(Fin n) with `ℒ'` ambient-primitive in `ℒ` (i.e. `ℒ' = ℒ ∩ spanℝ(ℒ')`), the orthogonal
projection of `ℒ` onto the complement of `S := spanℝ(ℒ')` is again a discrete lattice. -/
theorem discreteTopology_quotLattice {n : ℕ}
    (ℒ' ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hS : S = Submodule.span ℝ (ℒ' : Set (EuclideanSpace ℝ (Fin n))))
    (hprim : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ ℒ' ↔ x ∈ ℒ ∧ x ∈ S) :
    DiscreteTopology
      (ℒ.map (((Submodule.orthogonal S).starProjection :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).restrictScalars ℤ)) := by
  classical
  let p : E n →ₗ[ℝ] E n := (Submodule.orthogonal S).starProjection
  let pz : E n →ₗ[ℤ] E n := p.restrictScalars ℤ
  let L0 : Submodule ℤ ℒ := Submodule.comap (Submodule.subtype ℒ) ℒ'
  let b := Module.Free.chooseBasis ℤ ℒ
  obtain ⟨n0, o, hno, bO, bN, a, hsnf⟩ :=
    Submodule.exists_smith_normal_form_of_le b L0 (⊤ : Submodule ℤ ℒ) le_top
  let bL : Basis (Fin o) ℤ ℒ := bO.map (LinearEquiv.ofTop (⊤ : Submodule ℤ ℒ) rfl)
  let e : Fin o → E n := fun i => (bL i : E n)
  let J : Type := {j : Fin o // n0 ≤ j.val}
  let v : J → E n := fun j => p (e (j : Fin o))
  have hE : LinearIndependent ℝ e := linearIndependent_ambient_basis n ℒ bL
  have he_memS : ∀ i : Fin n0, e (Fin.castLE hno i) ∈ S := by
    intro i
    have hNz : (a i : ℤ) ≠ 0 := by
      intro h0
      have hrel : ((bN i : L0) : ℒ) = 0 := by
        simpa [h0] using (hsnf i)
      have hbN : (bN i : L0) ≠ 0 := Basis.ne_zero bN i
      apply hbN
      apply Subtype.ext
      exact hrel
    have hR : (a i : ℝ) ≠ 0 := by exact_mod_cast hNz
    have hrelE' : (a i : ℝ) • e (Fin.castLE hno i) = (((bN i : L0) : ℒ) : E n) := by
      have hval := congrArg (fun x : ℒ => (x : E n)) (hsnf i)
      simpa [e, bL, Int.cast_smul_eq_zsmul] using hval.symm
    have hNmemL' : (((bN i : L0) : ℒ) : E n) ∈ ℒ' := by
      exact (Submodule.mem_comap.mp ((bN i : L0).2))
    have hNmemS : (((bN i : L0) : ℒ) : E n) ∈ S := by
      exact (hprim _).mp hNmemL' |>.2
    have heq : e (Fin.castLE hno i) = (a i : ℝ)⁻¹ • (((bN i : L0) : ℒ) : E n) := by
      rw [← hrelE']
      rw [smul_smul]
      rw [inv_mul_cancel₀ hR, one_smul]
    rw [heq]
    exact S.smul_mem ((a i : ℝ)⁻¹) hNmemS
  have heSpanZ : span ℤ (Set.range e) = ℒ := by
    have h1 : Submodule.map (Submodule.subtype ℒ) (span ℤ (Set.range bL)) = span ℤ (Set.range e) := by
      rw [Submodule.map_span]
      congr
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨(bL i : ℒ), by simp⟩, ⟨i, rfl⟩, rfl⟩
    calc
      span ℤ (Set.range e) = Submodule.map (Submodule.subtype ℒ) (span ℤ (Set.range bL)) := h1.symm
      _ = Submodule.map (Submodule.subtype ℒ) ⊤ := by rw [bL.span_eq]
      _ = ℒ := by simp
  -- eC : the initial-segment subfamily (indices i < n0)
  let eC : Fin n0 → E n := fun i => e (Fin.castLE hno i)
  -- S equals the real span of the initial-segment subfamily
  have hS_span : S = span ℝ (Set.range eC) := by
    apply le_antisymm
    · -- S ≤ span ℝ (range eC): every element of ℒ' lies in span ℝ (range eC)
      rw [hS]
      refine span_le.mpr ?_
      rintro y hy
      -- y ∈ ℒ' ⊆ ℒ
      have hyL : y ∈ ℒ := (hprim y).mp hy |>.1
      let x : ℒ := ⟨y, hyL⟩
      have hm : x ∈ L0 := by
        dsimp [L0]
        exact (Submodule.mem_comap).mpr hy
      rcases (Module.Basis.mem_submodule_iff' bN).mp hm with ⟨c, hc⟩
      -- hc : x = ∑ i, c i • (bN i : ℒ)
      have hcE := congrArg (fun w : ℒ => (w : E n)) hc
      -- y = ∑ i, c i • ((bN i : ℒ) : E)
      have hyE : y = ∑ i : Fin n0, (c i : ℤ) • (((bN i : L0) : ℒ) : E n) := by
        simpa [x] using hcE
      -- each ((bN i : L0) : ℒ : E) = (a i : ℝ) • eC i
      have hbN_rel : ∀ i : Fin n0, (((bN i : L0) : ℒ) : E n) = (a i : ℝ) • eC i := by
        intro i
        have hval := congrArg (fun x : ℒ => (x : E n)) (hsnf i)
        have hrel : (a i : ℝ) • eC i = (((bN i : L0) : ℒ) : E n) := by
          simpa [eC, e, bL, Int.cast_smul_eq_zsmul] using hval.symm
        exact hrel.symm
      -- express y as an element of the real span of the eC i
      have hsum_mem : (∑ i : Fin n0, (c i : ℤ) • (((bN i : L0) : ℒ) : E n)) ∈ span ℝ (Set.range eC) := by
        refine Submodule.sum_mem _ ?_
        intro i hi
        have h1 : (((bN i : L0) : ℒ) : E n) ∈ span ℝ (Set.range eC) := by
          rw [hbN_rel i]
          exact (span ℝ (Set.range eC)).smul_mem (a i : ℝ) (subset_span ⟨i, rfl⟩)
        have hv : (c i : ℤ) • (((bN i : L0) : ℒ) : E n) = (c i : ℝ) • (((bN i : L0) : ℒ) : E n) :=
          (Int.cast_smul_eq_zsmul (R := ℝ) (c i) (((bN i : L0) : ℒ) : E n)).symm
        rw [hv]
        exact (span ℝ (Set.range eC)).smul_mem (c i : ℝ) h1
      rw [hyE]
      exact hsum_mem
    · -- span ℝ (range eC) ≤ S
      refine span_le.mpr ?_
      rintro x ⟨i, rfl⟩
      exact he_memS i
  -- the initial-segment subfamily and the projected complement family are ℝ-independent
  -- the full basis e is ℝ-independent; restrict to J
  have hsub_inj : Function.Injective (fun j : J => (j : Fin o)) := by
    intro a b h
    apply Subtype.ext
    exact h
  have hEJ : LinearIndependent ℝ (fun j : J => e (j : Fin o)) :=
    LinearIndependent.comp hE (fun j : J => (j : Fin o)) hsub_inj
  -- disjointness of the real spans of the two index blocks:
  have hdisj : ∀ z : E n, z ∈ span ℝ (Set.range (fun j : J => e (j : Fin o))) →
      z ∈ span ℝ (Set.range eC) → z = 0 := by
    intro z hzJ hzC
    rcases (mem_span_range_iff_exists_fun (R := ℝ) (v := fun j : J => e (j : Fin o)) (x := z)).1 hzJ with ⟨α, hα⟩
    rcases (mem_span_range_iff_exists_fun (R := ℝ) (v := eC) (x := z)).1 hzC with ⟨β, hβ⟩
    let T := Fin n0 ⊕ J
    let finj : T → Fin o := Sum.elim (Fin.castLE hno) (fun j : J => (j : Fin o))
    have hfinj_inj : Function.Injective finj := by
      intro a b h
      cases a with
      | inl i =>
        cases b with
        | inl j =>
          simp [finj] at h
          congr
        | inr j =>
          exfalso
          have h1 : (Fin.castLE hno i : Fin o).val = (j : Fin o).val := congrArg Fin.val h
          simp at h1
          omega
      | inr i =>
        cases b with
        | inl j =>
          exfalso
          have h1 : (i : Fin o).val = (Fin.castLE hno j : Fin o).val := congrArg Fin.val h
          simp at h1
          omega
        | inr j =>
          have hij : (i : Fin o) = (j : Fin o) := by simpa [finj] using h
          exact congrArg Sum.inr (Subtype.ext hij)
    have hTlin : LinearIndependent ℝ (fun t : T => e (finj t)) :=
      LinearIndependent.comp hE finj hfinj_inj
    let a : T → ℝ := Sum.elim (fun i : Fin n0 => -β i) α
    have hzero : (∑ t : T, a t • e (finj t)) = 0 := by
      calc
        (∑ t : T, a t • e (finj t))
            = (∑ i : Fin n0, (-β i) • e (Fin.castLE hno i)) + ∑ j : J, α j • e (j : Fin o) := by
                dsimp [T, a, finj]
                simp
        _ = -(∑ i : Fin n0, β i • e (Fin.castLE hno i)) + ∑ j : J, α j • e (j : Fin o) := by simp
        _ = -z + z := by
                dsimp [eC] at hβ
                rw [hα, hβ]
        _ = 0 := by simp
    have ha0 : ∀ t : T, a t = 0 := (Fintype.linearIndependent_iff.mp hTlin) a hzero
    have hα0 : ∀ j : J, α j = 0 := by
      intro j
      simpa [a] using ha0 (Sum.inr j)
    calc
      z = ∑ j : J, α j • e (j : Fin o) := hα.symm
      _ = 0 := by simp [hα0]
  -- the projected complement family is ℝ-independent
  have hJind : LinearIndependent ℝ (fun j : J => p (e (j : Fin o))) := by
    rw [Fintype.linearIndependent_iff]
    intro γ hγ
    let w : E n := ∑ j : J, γ j • e (j : Fin o)
    have hpw : p w = 0 := by
      calc
        p w = ∑ j : J, γ j • p (e (j : Fin o)) := by
              dsimp [w]
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro j hj
              rw [map_smul]
        _ = 0 := hγ
    have hwS : w ∈ S := mem_of_proj_orth_eq_zero n S hpw
    have hwC : w ∈ span ℝ (Set.range eC) := by
      simpa [hS_span] using hwS
    have hwJ : w ∈ span ℝ (Set.range (fun j : J => e (j : Fin o))) := by
      exact (mem_span_range_iff_exists_fun (R := ℝ) (v := fun j : J => e (j : Fin o)) (x := w)).2 ⟨γ, rfl⟩
    have hw0 : w = 0 := hdisj w hwJ hwC
    exact (Fintype.linearIndependent_iff.mp hEJ) γ (by
      simpa [w] using hw0)
  -- the quotient lattice equals the ℤ-span of the projected complement family
  have hMmap : Submodule.map pz ℒ = span ℤ (pz '' Set.range e) := by
    calc
      Submodule.map pz ℒ = Submodule.map pz (span ℤ (Set.range e)) := by rw [heSpanZ]
      _ = span ℤ (pz '' Set.range e) := by rw [Submodule.map_span]
  have hM1 : span ℤ (pz '' Set.range e) = span ℤ (Set.range v) := by
    apply le_antisymm
    · -- pz '' (range e) ⊆ span(range v)
      refine span_le.mpr ?_
      rintro x ⟨k, hke, hx⟩
      rcases hke with ⟨i, hi⟩
      subst k
      by_cases hk : i.val < n0
      · have hk_eq : i = Fin.castLE hno ⟨i.val, hk⟩ := by
          ext; simp
        have hekS : e i ∈ S := by
          rw [hk_eq]
          exact he_memS ⟨i.val, hk⟩
        have hp0 : p (e i) = 0 := proj_orth_eq_zero_of_mem n S hekS
        have hpz0 : pz (e i) = 0 := by simpa [pz] using hp0
        rw [← hx, hpz0]
        exact Submodule.zero_mem _
      · have hkJ : n0 ≤ i.val := (not_lt.mp hk)
        have hx' : pz (e i) = v ⟨i, hkJ⟩ := rfl
        rw [← hx, hx']
        exact subset_span ⟨⟨i, hkJ⟩, rfl⟩
    · -- span(range v) ⊆ pz '' (range e)
      refine span_le.mpr ?_
      rintro x ⟨j, rfl⟩
      exact subset_span ⟨e (j : Fin o), ⟨⟨(j : Fin o), rfl⟩, by simp [v, pz]⟩⟩
  have hMspan : Submodule.map pz ℒ = span ℤ (Set.range v) := by
    rw [hMmap, hM1]
  -- reindex the family to Fin
  let eJ : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let w : Fin (Fintype.card J) → E n := fun k => v (eJ.symm k)
  have hrangev : Set.range w = Set.range v := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨eJ.symm k, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨eJ j, by simp [w]⟩
  have hMspanW : Submodule.map pz ℒ = span ℤ (Set.range w) := by
    rw [hMspan, hrangev]
  -- ℝ-independence of the reindexed projected family
  have hwlin : LinearIndependent ℝ w := by
    dsimp [w]
    exact LinearIndependent.comp hJind (fun k : Fin (Fintype.card J) => eJ.symm k) (Equiv.injective eJ.symm)
  -- conclude
  change DiscreteTopology (Submodule.map pz ℒ)
  rw [hMspanW]
  exact discreteTopology_span_linIndep (n := n) (k := Fintype.card J) w hwlin
