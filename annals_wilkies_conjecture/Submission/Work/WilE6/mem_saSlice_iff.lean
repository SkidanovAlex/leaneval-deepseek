/-
  WilE6 (area E6): fibrewise closure and frontier of EA sets (Gabrielov 1998).

  Slicing an `SA (m+n)`-set at the origin of its `n`-dimensional fibre, via the
  *substitution* `sliceMap m n` (keep the first `m` coordinates, send the last `n` to `0`).

  The main content is that the substitution commutes with evaluation:
  `eval (sliceHom m n Q) w = eval Q (Fin.append w 0)`, whence membership in the slice is
  membership of the "padded" point in the original set.
-/
import Mathlib
import Submission.Work.WilE6.Closure

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## §1. The value of `Fin.append w 0` at an arbitrary index -/

/-- `Fin.append w 0` evaluated at `i : Fin (m+n)` is `w i` when `i < m` and `0` otherwise. -/
theorem fin_append_zero_apply (m n : ℕ) (w : Fin m → ℝ) (i : Fin (m + n)) :
    Fin.append w (0 : Fin n → ℝ) i = if h : i.1 < m then w ⟨i.1, h⟩ else 0 := by
  rw [Fin.append, Fin.addCases]
  split_ifs with h
  · rfl
  · simp

/-! ## §2. The substitution `sliceHom` commutes with evaluation -/

/-- Substituting `0` for the last `n` coordinates of an `SA (m+n)`-polynomial and evaluating at
`w` gives the value of the original polynomial at the padded point `Fin.append w 0`. -/
theorem eval_sliceHom (m n : ℕ) (Q : EAPoly (m + n) 0) (w : Fin m → ℝ) :
    MvPolynomial.eval (Sum.elim w (fun i : Fin 0 => i.elim0)) (sliceHom m n Q) =
      MvPolynomial.eval (Sum.elim (Fin.append w 0) (fun i : Fin 0 => i.elim0)) Q := by
  unfold sliceHom
  rw [Work.WilE6.eval_saPoly]
  change (MvPolynomial.eval w) (MvPolynomial.eval₂ MvPolynomial.C (sliceMap m n)
    (saUnpoly (m + n) Q)) = _
  rw [← MvPolynomial.eval_assoc]
  rw [saUnpoly, MvPolynomial.eval_rename]
  have hfun : ((⇑(MvPolynomial.eval w) ∘ sliceMap m n) ∘ ⇑(sumFin0Equiv (m + n))) =
      Sum.elim (Fin.append w 0) (fun i : Fin 0 => i.elim0) := by
    funext s
    rcases s with i | j
    · show MvPolynomial.eval w (sliceMap m n i) = Fin.append w 0 i
      rw [fin_append_zero_apply]
      unfold sliceMap
      split_ifs with h
      · simp
      · simp
    · exact j.elim0
  rw [hfun]

/-! ## §3. `holds` is preserved by the slice -/

/-- The sliced basic set, evaluated at `w`, holds exactly when the original basic set holds at
the padded point `Fin.append w 0`. -/
theorem basicSlice_holds (m n : ℕ) (B : Basic (m + n) 0) (w : Fin m → ℝ) :
    (⟨B.eqs.map (sliceHom m n), B.pos.map (sliceHom m n)⟩ : Basic m 0).holds
        (EAChain.nil m) w ↔
      B.holds (EAChain.nil (m + n)) (Fin.append w 0) := by
  constructor
  · rintro ⟨heq, hpos⟩
    refine ⟨?_, ?_⟩
    · intro Q hQ
      have h := heq (sliceHom m n Q) (List.mem_map.mpr ⟨Q, hQ, rfl⟩)
      simpa only [eaEval_nil, eval_sliceHom] using h
    · intro Q hQ
      have h := hpos (sliceHom m n Q) (List.mem_map.mpr ⟨Q, hQ, rfl⟩)
      simpa only [eaEval_nil, eval_sliceHom] using h
  · rintro ⟨heq, hpos⟩
    refine ⟨?_, ?_⟩
    · intro Q hQ
      obtain ⟨Q₀, hQ₀, rfl⟩ := List.mem_map.mp hQ
      have h := heq Q₀ hQ₀
      simpa only [eaEval_nil, eval_sliceHom] using h
    · intro Q hQ
      obtain ⟨Q₀, hQ₀, rfl⟩ := List.mem_map.mp hQ
      have h := hpos Q₀ hQ₀
      simpa only [eaEval_nil, eval_sliceHom] using h

/-! ## §4. Membership in the slice -/

/-- Membership in the slice at the origin of the fibre is membership of the padded point. -/
theorem mem_saSlice_iff (m n : ℕ) (X : WilkiesDesign.E.SA (m + n)) (w : Fin m → ℝ) :
    w ∈ (Work.WilE6.saSlice m n X).set ↔ Fin.append w (0 : Fin n → ℝ) ∈ X.set := by
  constructor
  · rintro ⟨B', hB', hB'holds⟩
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hB'
    exact ⟨B, hB, (basicSlice_holds m n B w).mp hB'holds⟩
  · rintro ⟨B, hB, hBholds⟩
    exact ⟨⟨B.eqs.map (sliceHom m n), B.pos.map (sliceHom m n)⟩,
      List.mem_map.mpr ⟨B, hB, rfl⟩, (basicSlice_holds m n B w).mpr hBholds⟩

end Work.WilE6
