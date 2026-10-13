import Mathlib
import Submission.Work.WilG5.Defs

/-!
  `Work.WilG5.Rel.graphOf_RelSel_mem`.

  A single-valued relation `R ⊆ ℝ^{d+n}` (single valued on the `u`-part) is turned by `RelSel`
  into the function `u ↦ RelSel R u`, and we need the *graph* of the coordinate `i` of that
  function, affinely transformed: the graph of `t ↦ c * RelSel R t i + m`.

  Strategy.  Denote `V := vgraph (RelSel R) ⊆ ℝ^{d+n}`.  The desired set is

      G = {z : Fin (d+1) → ℝ | z (last d) = c * (RelSel R (init z)) i + m}
        = { (u,w) | ∃ x, (u,x) ∈ V ∧ w = c * x i + m }

  (because `V` is exactly the graph of `RelSel R`, so `(u,x) ∈ V ↔ RelSel R u = x`).
  Reading the ambient `ℝ^{d+n+1}` as `(u,x,w)` (`u` first `d` coordinates, `x` the next `n`,
  `w` last), this is

      G = coordImage (keepι d n) (liftFirst 1 V ∩ Σ)

  where `Σ` is the hyperplane `w = c * x_i + m` (an `Ω`-set by `SOMin.hyp`) and `keepι d n`
  is the index map `Fin (d+1) → Fin (d+n+1)` keeping the first `d` coordinates and the last one.

  Membership bounds: `vgraph (RelSel R) = R ∪ vgraphExtra` where the extra piece is a
  complement-of-projection set of degree `B + const`, so `V` has degree `2B + const`; the
  remaining operations (`liftFirst`, intersection with a hyperplane, `coordImage`) add only
  constants to the degree and add constants plus one copy of `A₀` to the format, which is the
  shape asserted by the statement (`A + A₀`, `C * B + L` with `C = 2`).
-/

namespace Work.WilG5.Rel

open WilkiesDesign Work.WilG5

/-! ## Auxiliary definitions -/

/-- The index map `Fin (d+1) → Fin (d+n+1)` keeping the first `d` coordinates and the last one. -/
private def keepι (d n : ℕ) : Fin (d + 1) → Fin (d + n + 1) :=
  Fin.append (fun i : Fin d => (Fin.castAdd n i).castSucc) (fun _ : Fin 1 => Fin.last (d + n))

private theorem keepι_castAdd (d n : ℕ) (i : Fin d) :
    keepι d n (Fin.castAdd 1 i) = (Fin.castAdd n i).castSucc := Fin.append_left _ _ i

private theorem keepι_last (d n : ℕ) : keepι d n (Fin.last d) = Fin.last (d + n) := by
  have h : Fin.last d = Fin.natAdd d (0 : Fin 1) := Fin.ext rfl
  rw [h]; exact Fin.append_right _ _ _

/-- The hyperplane `w = c * x i + m`, where `y ∈ ℝ^{d+n+1}` reads as `(u, x, w)`. -/
private def relHyp (d n : ℕ) (i : Fin n) (c m : ℝ) : Set (Fin (d + n + 1) → ℝ) :=
  {y | y (Fin.last (d + n)) = c * y ((Fin.natAdd d i).castSucc) + m}

/-- The `R`-complement piece of `vgraph (RelSel R)`. -/
private def vgraphExtra (d n : ℕ) (R : Set (Fin (d + n) → ℝ)) : Set (Fin (d + n) → ℝ) :=
  liftFirst n (projN n R)ᶜ ∩ {z : Fin (d + n) → ℝ | (fun j : Fin n => z (Fin.natAdd d j)) = 0}

/-! ## The set-theoretic identity -/

private theorem graphOf_RelSel_eq {d n : ℕ} (R : Set (Fin (d + n) → ℝ)) (i : Fin n) (c m : ℝ) :
    graphOf (fun t : Fin d → ℝ => c * RelSel R t i + m) =
      coordImage (keepι d n) (liftFirst 1 (vgraph (RelSel R)) ∩ relHyp d n i c m) := by
  ext v
  constructor
  · intro hv
    simp only [graphOf, Set.mem_ofPred_eq] at hv
    refine ⟨Fin.snoc (α := fun _ => ℝ) (Fin.append (Fin.init v) (RelSel R (Fin.init v)))
      (v (Fin.last d)), ⟨?_, ?_⟩, ?_⟩
    · change (fun i' : Fin (d+n) => Fin.snoc (α := fun _ => ℝ)
        (Fin.append (Fin.init v) (RelSel R (Fin.init v))) (v (Fin.last d))
        (Fin.castAdd 1 i')) ∈ vgraph (RelSel R)
      have h1 : (fun i' : Fin (d+n) => Fin.snoc (α := fun _ => ℝ)
          (Fin.append (Fin.init v) (RelSel R (Fin.init v))) (v (Fin.last d))
          (Fin.castAdd 1 i')) = Fin.append (Fin.init v) (RelSel R (Fin.init v)) := by
        funext i'
        rw [show (Fin.castAdd 1 i' : Fin (d+n+1)) = Fin.castSucc i' from rfl, Fin.snoc_castSucc]
      rw [h1]
      exact (vgraph_append (RelSel R) (Fin.init v) (RelSel R (Fin.init v))).2 rfl
    · simp only [relHyp, Set.mem_ofPred_eq]
      rw [Fin.snoc_last]
      rw [show (Fin.snoc (α := fun _ => ℝ) (Fin.append (Fin.init v) (RelSel R (Fin.init v)))
        (v (Fin.last d)) ((Fin.natAdd d i).castSucc))
        = Fin.append (Fin.init v) (RelSel R (Fin.init v)) (Fin.natAdd d i) from by
          rw [Fin.snoc_castSucc]]
      rw [Fin.append_right]
      exact hv
    · funext j
      revert j
      refine Fin.addCases (motive := fun j => Fin.snoc (α := fun _ => ℝ)
        (Fin.append (Fin.init v) (RelSel R (Fin.init v))) (v (Fin.last d)) (keepι d n j) = v j)
        ?_ ?_
      · intro i'
        rw [keepι_castAdd]
        rw [Fin.snoc_castSucc]
        rw [Fin.append_left]
        rfl
      · intro k
        have hk : k = 0 := Fin.eq_zero k
        subst hk
        rw [show Fin.natAdd d (0 : Fin 1) = Fin.last d from Fin.ext rfl, keepι_last,
          Fin.snoc_last]
  · rintro ⟨y, ⟨hyV, hyH⟩, hyv⟩
    simp only [relHyp, Set.mem_ofPred_eq] at hyH
    simp only [graphOf, Set.mem_ofPred_eq]
    have hyV' : Fin.init y ∈ vgraph (RelSel R) := hyV
    rw [vgraph_iff] at hyV'
    have hidx : (fun i' : Fin d => Fin.init y (Fin.castAdd n i')) = Fin.init v := by
      funext i'
      rw [show Fin.init y (Fin.castAdd n i') = y ((Fin.castAdd n i').castSucc) from rfl]
      rw [← keepι_castAdd d n i']
      rw [show y (keepι d n (Fin.castAdd 1 i')) = v (Fin.castAdd 1 i') from
        congrFun hyv (Fin.castAdd 1 i')]
      rfl
    rw [hidx] at hyV'
    rw [show v (Fin.last d) = y (keepι d n (Fin.last d)) from (congrFun hyv (Fin.last d)).symm,
      keepι_last, hyH]
    rw [congrFun hyV' i]
    rfl

/-! ## The hyperplane is an `Ω`-set -/

private theorem relHyp_mem (S : WilkiesDesign.SOMin) {d n : ℕ} (i : Fin n) (c m : ℝ) :
    relHyp d n i c m ∈ S.Ω (d + n + 1) 1 (d + n + 1) := by
  have hdeg : (MvPolynomial.X (Fin.last (d+n)) - MvPolynomial.C c *
      MvPolynomial.X ((Fin.natAdd d i).castSucc) - MvPolynomial.C m :
      MvPolynomial (Fin (d+n+1)) ℝ).totalDegree ≤ 1 := by
    refine le_trans (td_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans (td_sub_le _ _) (max_le ?_ ?_)
      · exact td_X_le _
      · refine le_trans (td_mul_le _ _)
          (le_trans (add_le_add (td_C_le c) (td_X_le _)) (by norm_num))
    · exact le_trans (td_C_le m) (by norm_num)
  have heq : relHyp d n i c m = {z : Fin (d+n+1) → ℝ |
      MvPolynomial.eval z (MvPolynomial.X (Fin.last (d+n)) - MvPolynomial.C c *
        MvPolynomial.X ((Fin.natAdd d i).castSucc) - MvPolynomial.C m :
        MvPolynomial (Fin (d+n+1)) ℝ) = 0} := by
    ext z
    simp only [relHyp, Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact mem_mono (S.hyp (d+n+1) (MvPolynomial.X (Fin.last (d+n)) - MvPolynomial.C c *
      MvPolynomial.X ((Fin.natAdd d i).castSucc) - MvPolynomial.C m :
      MvPolynomial (Fin (d+n+1)) ℝ)) (d+n+1) 1 (le_refl _) hdeg

/-! ## The main lemma -/

theorem graphOf_RelSel_mem (S : WilkiesDesign.SOMin) {d n : ℕ} (i : Fin n) (c m : ℝ) :
    ∃ (A C L : ℕ), ∀ (A₀ B : ℕ) (R : Set (Fin (d + n) → ℝ)), R ∈ S.Ω A₀ B (d + n) →
      (∀ u : Fin d → ℝ, (∃ x : Fin n → ℝ, Fin.append u x ∈ R) →
        ∀ x y : Fin n → ℝ, Fin.append u x ∈ R → Fin.append u y ∈ R → x = y) →
      WilkiesDesign.graphOf (fun t : Fin d → ℝ => c * Work.WilG5.RelSel R t i + m) ∈
        S.Ω (A + A₀) (C * B + L) (d + 1) := by
  refine ⟨(2*n + 1 + (d+n+1)) + 2 + (d+n+1) + 1 + 64*((d+n+1)+(d+1)) + 64, 2,
    (2*n+4) + 1 + 32*((d+n+1)+(d+1)) + 32, ?_⟩
  intro A₀ B R hR huniq
  -- the `vgraph` of the selected function
  have hP : projN n R ∈ S.Ω (A₀ + n) B d := projN_mem (S := S) n A₀ B hR
  have hPc : (projN n R)ᶜ ∈ S.Ω (A₀ + n + 1) B d := S.compl hP
  have hL : liftFirst n (projN n R)ᶜ ∈ S.Ω (A₀ + n + 1 + n) B (d + n) :=
    liftFirst_mem (S := S) n (A₀ + n + 1) B hPc
  have hZ : ({z : Fin (d + n) → ℝ | (fun j : Fin n => z (Fin.natAdd d j)) = 0}) ∈
      S.Ω (d + n + 1) (2 * n + 4) (d + n) := zeroTail_mem (S := S)
  have hL' : liftFirst n (projN n R)ᶜ ∈ S.Ω (A₀ + (2*n + 1 + (d+n+1))) B (d + n) :=
    mem_mono hL _ B (by omega) (le_refl B)
  have hZ' : ({z : Fin (d + n) → ℝ | (fun j : Fin n => z (Fin.natAdd d j)) = 0}) ∈
      S.Ω (A₀ + (2*n + 1 + (d+n+1))) (2 * n + 4) (d + n) :=
    mem_mono hZ _ _ (by omega) (le_refl _)
  have hE := S.inter (fun j : Fin 2 => if j = 0 then B else 2 * n + 4)
      (fun j : Fin 2 => if j = 0 then liftFirst n (projN n R)ᶜ
        else {z : Fin (d + n) → ℝ | (fun j' : Fin n => z (Fin.natAdd d j')) = 0})
      (by intro j
          fin_cases j
          · simpa using hL'
          · simpa using hZ')
  rw [show (∑ j : Fin 2, (if j = 0 then B else 2 * n + 4)) = B + (2 * n + 4) from by
    simp [Fin.sum_univ_two]] at hE
  have hEset : (⋂ j : Fin 2, (if j = 0 then liftFirst n (projN n R)ᶜ
        else {z : Fin (d + n) → ℝ | (fun j' : Fin n => z (Fin.natAdd d j')) = 0})) =
      vgraphExtra d n R := by
    ext z; simp [vgraphExtra, Fin.forall_fin_two]
  rw [hEset] at hE
  -- `R ∪ vgraphExtra` is `vgraph (RelSel R)`
  have hR'' : R ∈ S.Ω (A₀ + (2*n + 1 + (d+n+1)) + 1) B (d + n) :=
    mem_mono hR _ B (by omega) (le_refl B)
  have hE'' : vgraphExtra d n R ∈ S.Ω (A₀ + (2*n + 1 + (d+n+1)) + 1) (B + (2 * n + 4))
      (d + n) := mem_mono hE _ _ (by omega) (le_refl _)
  have hU := S.union (fun j : Fin 2 => if j = 0 then B else B + (2 * n + 4))
      (fun j : Fin 2 => if j = 0 then R else vgraphExtra d n R)
      (by intro j
          fin_cases j
          · simpa using hR''
          · simpa using hE'')
  rw [show (∑ j : Fin 2, (if j = 0 then B else B + (2 * n + 4))) = B + (B + (2 * n + 4))
    from by simp [Fin.sum_univ_two]] at hU
  have hUset : (⋃ j : Fin 2, (if j = 0 then R else vgraphExtra d n R)) =
      R ∪ vgraphExtra d n R := by
    ext z; simp [Fin.exists_fin_two]
  rw [hUset] at hU
  have hvgraph : vgraph (RelSel R) = R ∪ vgraphExtra d n R := by
    rw [vgraph_RelSel R huniq]
    congr 1
  rw [← hvgraph] at hU
  -- lift to `(u, x, w)` and intersect with the hyperplane
  have hV1 : liftFirst 1 (vgraph (RelSel R)) ∈
      S.Ω (A₀ + (2*n + 1 + (d+n+1)) + 1 + 1) (B + (B + (2 * n + 4))) (d + n + 1) :=
    liftFirst_mem (S := S) 1 (A₀ + (2*n + 1 + (d+n+1)) + 1) (B + (B + (2 * n + 4))) hU
  have hV1' : liftFirst 1 (vgraph (RelSel R)) ∈
      S.Ω (A₀ + ((2*n + 1 + (d+n+1)) + 2 + (d+n+1))) (B + (B + (2 * n + 4)))
        (d + n + 1) := mem_mono hV1 _ _ (by omega) (le_refl _)
  have hSig' : relHyp d n i c m ∈
      S.Ω (A₀ + ((2*n + 1 + (d+n+1)) + 2 + (d+n+1))) 1 (d + n + 1) :=
    mem_mono (relHyp_mem (S := S) i c m) _ 1 (by omega) (le_refl _)
  have hA := S.inter (fun j : Fin 2 => if j = 0 then B + (B + (2 * n + 4)) else 1)
      (fun j : Fin 2 => if j = 0 then liftFirst 1 (vgraph (RelSel R)) else relHyp d n i c m)
      (by intro j
          fin_cases j
          · simpa using hV1'
          · simpa using hSig')
  rw [show (∑ j : Fin 2, (if j = 0 then B + (B + (2 * n + 4)) else 1)) =
      B + (B + (2 * n + 4)) + 1 from by simp [Fin.sum_univ_two]] at hA
  have hAset : (⋂ j : Fin 2,
      (if j = 0 then liftFirst 1 (vgraph (RelSel R)) else relHyp d n i c m)) =
      liftFirst 1 (vgraph (RelSel R)) ∩ relHyp d n i c m := by
    ext z; simp [Fin.forall_fin_two]
  rw [hAset] at hA
  -- forget the `x`-coordinates
  have hG := coordImage_mem (S := S) (m := d + 1) (N := d + n + 1) (ι := keepι d n)
      (F := A₀ + ((2*n + 1 + (d+n+1)) + 2 + (d+n+1)) + 1)
      (D := B + (B + (2 * n + 4)) + 1) hA
  rw [graphOf_RelSel_eq R i c m]
  exact mem_mono hG _ _ (by omega) (by omega)

end Work.WilG5.Rel
