import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Transform.flatIdx
import Submission.Work.DFT.dftDefs
import Submission.Work.DFT.digitsBij
import Submission.Work.DFT.subDigitsFacts
import Submission.Work.DFT.phaseLin
import Submission.Work.ConvR.negaNorm

/-!
# Paper Prop 3.5: the bridge `M_C(u,v) = U(M_R(T u, T v))`

This file proves `Work.Transform.convC_bridge`, the algebraic heart of paper Proposition 3.5:
the complex cyclic convolution over the dimension list `ts' ++ [r]` is transported by the
diagonal scalings `phiArrL` (paper's `T̃`, `w ↦ Σ_j ζ^j w_j y^j` coefficientwise) and
`psiFlatL` (`Ũ = T̃⁻¹`) to the synthetic (negacyclic) convolution `convR` over
`ℝ = ℂ[y]/(y^r+1)`.

The proof is a computation with the flat index `flatIdx ts' r a c = a*r + c`:

* `digitsAppend`: `digits (ts'++[r]) (a*r+c) = digits ts' a ++ [c]`;
* `subIdxFlatIdx`: `subIdx (ts'++[r]) (a*r+c) (a'*r+c') = subIdx ts' a a' * r + (c+r-c')%r`;
* `sumFlatIdx`: sums over `Fin ((ts'++[r]).prod)` split as double sums over `Fin ts'.prod × Fin r`;
* `negaMulZeta`: the coefficient-level diagonalisation `(ℂ^r, ∗) ≅ ℂ[y]/(y^r+1)`, `x ↦ ζ y`.
-/

open scoped BigOperators

namespace Work.Transform

open HvdH

/-! ## Digit arithmetic for the flat index -/

private lemma arith_mod (a r c P : ℕ) (hc : c < r) :
    (a * r + c) % (P * r) = (a % P) * r + c := by
  rcases Nat.eq_zero_or_pos P with hP | hP
  · subst hP; simp
  · have h : a * r + c = ((a % P) * r + c) + (P * r) * (a / P) := by
      have h1 := Nat.div_add_mod a P
      nlinarith [h1]
    rw [h, Nat.add_mul_mod_self_left]
    rw [Nat.mod_eq_of_lt]
    have h2 : a % P < P := Nat.mod_lt a hP
    nlinarith [Nat.mul_le_mul_right r (Nat.succ_le_of_lt h2)]

private lemma arith_div (a r c P : ℕ) (hr : 0 < r) (hc : c < r) :
    (a * r + c) / (P * r) = a / P := by
  rcases Nat.eq_zero_or_pos P with hP | hP
  · subst hP; simp
  · rw [Nat.mul_comm P r, ← Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm a r, Nat.mul_add_div hr, Nat.div_eq_of_lt hc, Nat.add_zero]

/-- Appending a least-significant digit in radix `r` to the mixed-radix expansion. -/
theorem digitsAppend (ts' : List ℕ) (r : ℕ) (hr : 0 < r) (a c : ℕ) (hc : c < r) :
    HvdH.digits (ts' ++ [r]) (a * r + c) = HvdH.digits ts' a ++ [c] := by
  induction ts' generalizing a with
  | nil =>
    simp only [List.nil_append, HvdH.digits, List.prod_nil, Nat.div_one]
    rw [Nat.mul_comm a r, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
  | cons t ts ih =>
    rw [List.cons_append, HvdH.digits, List.prod_append, List.prod_singleton,
      arith_div a r c ts.prod hr hc, arith_mod a r c ts.prod hc, ih (a % ts.prod),
      HvdH.digits, List.cons_append]

/-- Horner evaluation of a digit list with one more least-significant digit. -/
theorem undigitsAppend (ts' : List ℕ) (r d : ℕ) (X : List ℕ) (hX : X.length = ts'.length) :
    HvdH.undigits (ts' ++ [r]) (X ++ [d]) = HvdH.undigits ts' X * r + d := by
  induction ts' generalizing X with
  | nil =>
    have hX' : X = [] := List.eq_nil_of_length_eq_zero (by simpa using hX)
    subst hX'; simp [HvdH.undigits]
  | cons t ts ih =>
    obtain ⟨x, X', rfl⟩ : ∃ x X', X = x :: X' := by
      cases X with
      | nil => simp at hX
      | cons x X' => exact ⟨x, X', rfl⟩
    simp only [List.length_cons, Nat.succ.injEq] at hX
    show x * (ts ++ [r]).prod + HvdH.undigits (ts ++ [r]) (X' ++ [d])
        = (x * ts.prod + HvdH.undigits ts X') * r + d
    rw [List.prod_append, List.prod_singleton, ih X' hX]
    ring

/-- Componentwise subtraction of digit lists commutes with appending a last coordinate. -/
theorem subDigitsAppend (ts' : List ℕ) (r : ℕ) (X Y : List ℕ) (c c' : ℕ)
    (hX : X.length = ts'.length) (hY : Y.length = ts'.length) :
    HvdH.subDigits (ts' ++ [r]) (X ++ [c]) (Y ++ [c']) =
      HvdH.subDigits ts' X Y ++ [(c + r - c') % r] := by
  induction ts' generalizing X Y with
  | nil =>
    have hX' : X = [] := List.eq_nil_of_length_eq_zero (by simpa using hX)
    have hY' : Y = [] := List.eq_nil_of_length_eq_zero (by simpa using hY)
    subst hX'; subst hY'; simp [HvdH.subDigits]
  | cons t ts ih =>
    obtain ⟨x, X', rfl⟩ : ∃ x X', X = x :: X' := by
      cases X with
      | nil => simp at hX
      | cons x X' => exact ⟨x, X', rfl⟩
    obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
      cases Y with
      | nil => simp at hY
      | cons y Y' => exact ⟨y, Y', rfl⟩
    simp only [List.length_cons, Nat.succ.injEq] at hX hY
    show (x + t - y) % t :: HvdH.subDigits (ts ++ [r]) (X' ++ [c]) (Y' ++ [c'])
        = (x + t - y) % t :: (HvdH.subDigits ts X' Y' ++ [(c + r - c') % r])
    rw [ih X' Y' hX hY]

/-- `subDigits` preserves the common length of its two digit lists. -/
theorem subDigitsLength (ts X Y : List ℕ) (hX : X.length = ts.length)
    (hY : Y.length = ts.length) : (HvdH.subDigits ts X Y).length = ts.length := by
  induction ts generalizing X Y with
  | nil =>
    have hX' : X = [] := List.eq_nil_of_length_eq_zero (by simpa using hX)
    have hY' : Y = [] := List.eq_nil_of_length_eq_zero (by simpa using hY)
    subst hX'; subst hY'; simp [HvdH.subDigits]
  | cons t ts ih =>
    obtain ⟨x, X', rfl⟩ : ∃ x X', X = x :: X' := by
      cases X with
      | nil => simp at hX
      | cons x X' => exact ⟨x, X', rfl⟩
    obtain ⟨y, Y', rfl⟩ : ∃ y Y', Y = y :: Y' := by
      cases Y with
      | nil => simp at hY
      | cons y Y' => exact ⟨y, Y', rfl⟩
    simp only [List.length_cons, Nat.succ.injEq] at hX hY
    simp [HvdH.subDigits, ih X' Y' hX hY]

/-- The flat index of `j - k` splits as the flat index of the first coordinates plus the
wrapped last coordinate. -/
theorem subIdxFlatIdx (ts' : List ℕ) (r : ℕ) (hr : 0 < r)
    (a a' : Fin ts'.prod) (c c' : Fin r) :
    HvdH.subIdx (ts' ++ [r]) (flatIdx ts' r a c) (flatIdx ts' r a' c')
      = HvdH.subIdx ts' (a:ℕ) (a':ℕ) * r + ((c:ℕ) + r - (c':ℕ)) % r := by
  have hlen : (HvdH.digits ts' (a:ℕ)).length = ts'.length := Work.DFT.digits_length ts' (a:ℕ)
  have hlen' : (HvdH.digits ts' (a':ℕ)).length = ts'.length := Work.DFT.digits_length ts' (a':ℕ)
  simp only [HvdH.subIdx]
  rw [flatIdx_val, flatIdx_val,
    digitsAppend ts' r hr (a:ℕ) (c:ℕ) c.isLt, digitsAppend ts' r hr (a':ℕ) (c':ℕ) c'.isLt]
  rw [subDigitsAppend ts' r (HvdH.digits ts' (a:ℕ)) (HvdH.digits ts' (a':ℕ)) (c:ℕ) (c':ℕ)
    hlen hlen']
  rw [undigitsAppend ts' r _ _ (by rw [subDigitsLength ts' _ _ hlen hlen'])]

/-- Sums over `Fin ((ts' ++ [r]).prod)` split as double sums over `Fin ts'.prod × Fin r`
along the flat index `(a,c) ↦ a*r + c`. -/
theorem sumFlatIdx (ts' : List ℕ) (r : ℕ) (f : Fin ((ts' ++ [r]).prod) → ℂ) :
    ∑ k : Fin ((ts' ++ [r]).prod), f k = ∑ a : Fin ts'.prod, ∑ c : Fin r, f (flatIdx ts' r a c) := by
  have h : ts'.prod * r = (ts' ++ [r]).prod := by simp
  let e : Fin ts'.prod × Fin r ≃ Fin ((ts' ++ [r]).prod) :=
    finProdFinEquiv.trans (Fin.castOrderIso h).toEquiv
  have he : ∀ p : Fin ts'.prod × Fin r, e p = flatIdx ts' r p.1 p.2 := by
    intro p; apply Fin.ext
    simp [e, flatIdx, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  calc ∑ k : Fin ((ts' ++ [r]).prod), f k
      = ∑ p : Fin ts'.prod × Fin r, f (e p) := (Equiv.sum_comp e f).symm
    _ = ∑ a : Fin ts'.prod, ∑ c : Fin r, f (e (a,c)) := Fintype.sum_prod_type _
    _ = ∑ a : Fin ts'.prod, ∑ c : Fin r, f (flatIdx ts' r a c) := by simp [he]

/-! ## The diagonalisation of the negacyclic product -/

/-- Paper Prop 3.5, coefficient level: multiplying the `i`-th coefficient of `A` and `B` by
`ζ^i` (`ζ = e^{πi/r}`, `ζ^r = -1`) turns the negacyclic product `negaMul` in `ℂ[y]/(y^r+1)`
into the cyclic convolution `c ↦ Σ_{c'} A_{c'} B_{(c-c') mod r}`. -/
theorem negaMulZeta (r : ℕ) (hr : 0 < r) (A B : Fin r → ℂ) (c : Fin r) :
    (zeta r (c:ℕ))⁻¹ * HvdH.negaMul r (fun i => zeta r (i:ℕ) * A i)
      (fun i => zeta r (i:ℕ) * B i) c
      = ∑ c' : Fin r, A c' * B ⟨((c:ℕ) + r - (c':ℕ)) % r, Nat.mod_lt _ hr⟩ := by
  rw [Work.ConvR.negaMul_explicit, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : (i:ℕ) ≤ (c:ℕ)
  · rw [dif_pos hi]
    have hzi : zeta r (i:ℕ) * zeta r ((c:ℕ) - (i:ℕ)) = zeta r (c:ℕ) := by
      rw [← zeta_add]
      congr 1
      omega
    have hval : ((c:ℕ) + r - (i:ℕ)) % r = (c:ℕ) - (i:ℕ) := by
      have h1 : (c:ℕ) + r - (i:ℕ) = ((c:ℕ) - (i:ℕ)) + r * 1 := by omega
      rw [h1, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    have hB : B ⟨(c:ℕ) - (i:ℕ), by omega⟩ =
        B ⟨((c:ℕ) + r - (i:ℕ)) % r, Nat.mod_lt _ hr⟩ := by
      congr 1
      apply Fin.ext
      exact hval.symm
    rw [hB]
    calc (zeta r (c:ℕ))⁻¹ * ((zeta r (i:ℕ) * A i) *
            (zeta r ((c:ℕ) - (i:ℕ)) * B ⟨((c:ℕ) + r - (i:ℕ)) % r, Nat.mod_lt _ hr⟩))
        = ((zeta r (c:ℕ))⁻¹ * (zeta r (i:ℕ) * zeta r ((c:ℕ) - (i:ℕ)))) *
            (A i * B ⟨((c:ℕ) + r - (i:ℕ)) % r, Nat.mod_lt _ hr⟩) := by ring
      _ = ((zeta r (c:ℕ))⁻¹ * zeta r (c:ℕ)) *
            (A i * B ⟨((c:ℕ) + r - (i:ℕ)) % r, Nat.mod_lt _ hr⟩) := by rw [hzi]
      _ = A i * B ⟨((c:ℕ) + r - (i:ℕ)) % r, Nat.mod_lt _ hr⟩ := by
            rw [inv_mul_cancel₀ (zeta_ne_zero r (c:ℕ)), one_mul]
  · rw [dif_neg hi]
    push_neg at hi
    have hzi : zeta r (i:ℕ) * zeta r ((c:ℕ) + r - (i:ℕ)) = -(zeta r (c:ℕ)) := by
      rw [← zeta_add]
      have h1 : (i:ℕ) + ((c:ℕ) + r - (i:ℕ)) = (c:ℕ) + r := by omega
      rw [h1, zeta_add r (c:ℕ) r, zeta_self r hr]
      ring
    have hval : ((c:ℕ) + r - (i:ℕ)) % r = (c:ℕ) + r - (i:ℕ) := by
      exact Nat.mod_eq_of_lt (by omega)
    have hB : B ⟨(c:ℕ) + r - (i:ℕ), by omega⟩ =
        B ⟨((c:ℕ) + r - (i:ℕ)) % r, Nat.mod_lt _ hr⟩ := by
      congr 1
      apply Fin.ext
      exact hval.symm
    rw [hB]
    calc (zeta r (c:ℕ))⁻¹ * (-((zeta r (i:ℕ) * A i) *
            (zeta r ((c:ℕ) + r - (i:ℕ)) * B ⟨((c:ℕ) + r - (i:ℕ)) % r, Nat.mod_lt _ hr⟩)))
        = (-((zeta r (c:ℕ))⁻¹ * (zeta r (i:ℕ) * zeta r ((c:ℕ) + r - (i:ℕ))))) *
            (A i * B ⟨((c:ℕ) + r - (i:ℕ)) % r, Nat.mod_lt _ hr⟩) := by ring
      _ = ((zeta r (c:ℕ))⁻¹ * zeta r (c:ℕ)) *
            (A i * B ⟨((c:ℕ) + r - (i:ℕ)) % r, Nat.mod_lt _ hr⟩) := by rw [hzi]; ring
      _ = A i * B ⟨((c:ℕ) + r - (i:ℕ)) % r, Nat.mod_lt _ hr⟩ := by
            rw [inv_mul_cancel₀ (zeta_ne_zero r (c:ℕ)), one_mul]

/-! ## The scalings `T̃` and `Ũ` at a flat index -/

/-- The map `T̃` (paper Prop 3.5) applied at a pair of indices: it is the diagonal scaling by
`ζ^c` and the reindexing `w ↦ w ∘ flatIdx`. -/
theorem phiArrL_flatIdx (ts' : List ℕ) (r : ℕ) (w : Fin ((ts' ++ [r]).prod) → ℂ)
    (a : Fin ts'.prod) (c : Fin r) :
    phiArrL r ts' w a c = zeta r (c : ℕ) * w (flatIdx ts' r a c) := rfl

/-- The inverse map `Ũ = T̃⁻¹` at a flat index: diagonal scaling by `ζ^{-c}`. -/
theorem psiFlatL_flatIdx (ts' : List ℕ) (r : ℕ) (hr : 0 < r)
    (W : Fin ts'.prod → Fin r → ℂ) (j : Fin ts'.prod) (c : Fin r) :
    psiFlatL r ts' W (flatIdx ts' r j c) = (zeta r (c : ℕ))⁻¹ * W j c := by
  have hmod : (flatIdx ts' r j c : ℕ) % r = (c : ℕ) := flatIdx_mod ts' r hr j c
  have hdiv : (flatIdx ts' r j c : ℕ) / r = (j : ℕ) := flatIdx_div ts' r hr j c
  simp only [psiFlatL, hmod, hdiv]

/-! ## The bridge -/

/-- Paper Prop 3.5: the bridge between the complex convolution over `ts' ++ [r]` and the
synthetic convolution over `R` in dimension `(r, ts')`.  `phiArrL` (apply `w ↦ Σ_j ζ^j w_j y^j`,
which on coefficient vectors is the diagonal scaling by `ζ^c`) and its inverse `psiFlatL`
(diagonal scaling by `ζ^{-c}`) transport `convC (ts' ++ [r])` to `convR r ts'`. -/
theorem convC_bridge (ts' : List ℕ) (r : ℕ) (hr : 0 < r) (hpos : ∀ t ∈ ts', 0 < t)
    (u v : Fin ((ts' ++ [r]).prod) → ℂ) :
    HvdH.convC (ts' ++ [r]) u v
      = Work.Transform.psiFlatL r ts' (HvdH.convR r ts' (Work.Transform.phiArrL r ts' u)
          (Work.Transform.phiArrL r ts' v)) := by
  have key : ∀ (j : Fin ts'.prod) (c : Fin r),
      HvdH.convC (ts' ++ [r]) u v (flatIdx ts' r j c)
        = Work.Transform.psiFlatL r ts'
            (HvdH.convR r ts' (Work.Transform.phiArrL r ts' u)
              (Work.Transform.phiArrL r ts' v)) (flatIdx ts' r j c) := by
    intro j c
    have hNlt : ∀ (a : Fin ts'.prod) (c' : Fin r),
        HvdH.subIdx ts' (j:ℕ) (a:ℕ) * r + ((c:ℕ) + r - (c':ℕ)) % r
          < (ts' ++ [r]).prod := by
      intro a c'
      have h1 : HvdH.subIdx ts' (j:ℕ) (a:ℕ) < ts'.prod := Work.DFT.subIdx_lt ts' hpos j a
      have h2 : ((c:ℕ) + r - (c':ℕ)) % r < r := Nat.mod_lt _ hr
      simp only [List.prod_append, List.prod_singleton]
      nlinarith
    have hL : HvdH.convC (ts' ++ [r]) u v (flatIdx ts' r j c)
        = (1 / (((ts' ++ [r]).prod : ℕ) : ℂ)) * ∑ a : Fin ts'.prod, ∑ c' : Fin r,
            u (flatIdx ts' r a c')
              * v ⟨HvdH.subIdx ts' (j:ℕ) (a:ℕ) * r + ((c:ℕ) + r - (c':ℕ)) % r,
                  hNlt a c'⟩ := by
      rw [HvdH.convC, sumFlatIdx]
      congr 1
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro c' _
      rw [subIdxFlatIdx ts' r hr j a c c']
      simp only [HvdH.vget, dif_pos (hNlt a c')]
    have hR : Work.Transform.psiFlatL r ts'
          (HvdH.convR r ts' (Work.Transform.phiArrL r ts' u)
            (Work.Transform.phiArrL r ts' v)) (flatIdx ts' r j c)
        = (1 / (((ts' ++ [r]).prod : ℕ) : ℂ)) * ∑ a : Fin ts'.prod, ∑ c' : Fin r,
            u (flatIdx ts' r a c')
              * v ⟨HvdH.subIdx ts' (j:ℕ) (a:ℕ) * r + ((c:ℕ) + r - (c':ℕ)) % r,
                  hNlt a c'⟩ := by
      rw [psiFlatL_flatIdx ts' r hr _ j c]
      rw [HvdH.convR]
      rw [show ((ts'.prod * r : ℕ) : ℂ) = (((ts' ++ [r]).prod : ℕ) : ℂ) by simp]
      rw [← mul_assoc, mul_comm (zeta r (c:ℕ))⁻¹, mul_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl; intro a _
      have hsub : HvdH.subIdx ts' (j:ℕ) (a:ℕ) < ts'.prod :=
        Work.DFT.subIdx_lt ts' hpos j a
      have hU : (phiArrL r ts' u) a = (fun i : Fin r => zeta r (i:ℕ) * u (flatIdx ts' r a i)) := by
        funext i
        exact phiArrL_flatIdx ts' r u a i
      have hV : (fun c'' => if h : HvdH.subIdx ts' (j:ℕ) (a:ℕ) < ts'.prod
            then (phiArrL r ts' v) ⟨HvdH.subIdx ts' (j:ℕ) (a:ℕ), h⟩ c'' else 0)
          = (fun i : Fin r =>
              zeta r (i:ℕ) * v (flatIdx ts' r ⟨HvdH.subIdx ts' (j:ℕ) (a:ℕ), hsub⟩ i)) := by
        funext c''
        rw [dif_pos hsub]
        exact phiArrL_flatIdx ts' r v ⟨HvdH.subIdx ts' (j:ℕ) (a:ℕ), hsub⟩ c''
      rw [hU, hV]
      rw [negaMulZeta r hr (fun i => u (flatIdx ts' r a i))
        (fun i' => v (flatIdx ts' r ⟨HvdH.subIdx ts' (j:ℕ) (a:ℕ), hsub⟩ i')) c]
      apply Finset.sum_congr rfl; intro c' _
      congr 1
    exact hL.trans hR.symm
  funext i
  have hlt : (i:ℕ) < ts'.prod * r := by
    have h := i.isLt
    simpa [List.prod_append] using h
  have hdiv : (i:ℕ) / r < ts'.prod := (Nat.div_lt_iff_lt_mul hr).2 hlt
  have hmod : (i:ℕ) % r < r := Nat.mod_lt _ hr
  have hi : i = flatIdx ts' r ⟨(i:ℕ)/r, hdiv⟩ ⟨(i:ℕ)%r, hmod⟩ := by
    apply Fin.ext
    rw [flatIdx_val, Nat.mul_comm ((i:ℕ)/r) r]
    exact (Nat.div_add_mod i r).symm
  rw [hi]
  exact key _ _

end Work.Transform
