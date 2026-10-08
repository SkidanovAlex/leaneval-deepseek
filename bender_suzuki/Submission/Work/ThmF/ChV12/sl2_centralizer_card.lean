import Mathlib
import Submission.Work.ThmF.ChV12.torus_aux
import Submission.Work.ThmF.ChV12.norm_form_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- In `SL(2,F)` over a finite field `F` of characteristic two in which `X²+X+1` has no root,
the centralizer of an element `c` of order `3` has cardinality `|F| + 1`.

The element `c` is `3`-regular: its minimal polynomial is `X²+X+1`, so `F[c] ≅ F_{q²}` and
`c` lies in the non-split (Coxeter) torus of order `q + 1`. The centralizer is cut out by the
conic `x² + xy + y² = 1`, whose cardinality is `|F| + 1` (`norm_form_card`). -/
theorem sl2_centralizer_card {F : Type*} [Field F] [Fintype F] [CharP F 2] (n : ℕ)
    (hF : Nat.card F = 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    (c : Matrix.SpecialLinearGroup (Fin 2) F) (hc : orderOf c = 3) :
    Nat.card ↥(Subgroup.centralizer ({c} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) = 2 ^ n + 1 := by
  classical
  -- `X² + X + 1` has no root in `F`.
  have hroot : ∀ t : F, t ^ 2 + t + 1 ≠ 0 := by
    intro t ht
    exact torus_no_root (by rw [hF]; exact h3) t ht
  -- Matrix data of `c`.
  have hcsq : (c : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F)
      + (c : Matrix (Fin 2) (Fin 2) F) + 1 = 0 := sl2_order_three_sq c hc
  have hdetc : (c : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe c
  have htrc : (c : Matrix (Fin 2) (Fin 2) F).trace = 1 := sl2_trace_eq_one hdetc hcsq
  -- The trace of `p • 1 + q • c` is `q` (since `trace 1 = 2 = 0`).
  have htr_repr : ∀ p q : F,
      (p • (1 : Matrix (Fin 2) (Fin 2) F) + q • (c : Matrix (Fin 2) (Fin 2) F)).trace = q := by
    intro p q
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
        Fintype.card_fin, CharP.cast_eq_zero F 2, htrc]
    simp [smul_eq_mul]
  -- `p • 1 + q • c` is in `SL(2,F)` whenever `p² + pq + q² = 1`.
  have hdetP : ∀ p : {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1},
      (p.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + p.1.2 • (c : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
    intro p
    rw [det_smul_one_add_smul, htrc, hdetc]
    simpa only [mul_one] using p.2
  -- The underlying `SL(2,F)`-element of a point of the conic.
  let g : {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} →
      Matrix.SpecialLinearGroup (Fin 2) F :=
    fun p => ⟨p.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + p.1.2 • (c : Matrix (Fin 2) (Fin 2) F),
      hdetP p⟩
  -- It centralizes `c`, since it lies in `F[c]` (the span of `1` and `c`).
  have hmemP : ∀ p, g p * c = c * g p := by
    intro p
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    change ((p.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + p.1.2 • (c : Matrix (Fin 2) (Fin 2) F))
        * (c : Matrix (Fin 2) (Fin 2) F)) i j
      = ((c : Matrix (Fin 2) (Fin 2) F)
        * (p.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + p.1.2 • (c : Matrix (Fin 2) (Fin 2) F))) i j
    exact congrFun (congrFun ((matrix_centralizer_eq_span hcsq hroot
      (p.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + p.1.2 • (c : Matrix (Fin 2) (Fin 2) F))).mpr
      ⟨p.1.1, p.1.2, rfl⟩) i) j
  -- The map from the conic to the centralizer.
  let f : {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} →
      ↥(Subgroup.centralizer ({c} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) :=
    fun p => ⟨g p, Subgroup.mem_centralizer_singleton_iff.mpr (hmemP p)⟩
  -- Injectivity: `1` and `c` are linearly independent, and the trace recovers `q`.
  have hinj : Function.Injective f := by
    intro p p' hpp
    have hmat : p.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + p.1.2 • (c : Matrix (Fin 2) (Fin 2) F)
        = p'.1.1 • (1 : Matrix (Fin 2) (Fin 2) F) + p'.1.2 • (c : Matrix (Fin 2) (Fin 2) F) :=
      congrArg (fun z : ↥(Subgroup.centralizer ({c} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) =>
        ((z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hpp
    have h2 : p.1.2 = p'.1.2 := by
      have h := congrArg Matrix.trace hmat
      rw [htr_repr, htr_repr] at h
      exact h
    have h1 : p.1.1 = p'.1.1 := by
      rw [h2] at hmat
      have h := add_right_cancel hmat
      have h00 := congrFun (congrFun h 0) 0
      simpa using h00
    exact Subtype.ext (Prod.ext h1 h2)
  -- Surjectivity: every element of the centralizer is a quadratic polynomial in `c` with
  -- determinant `1`.
  have hsurj : Function.Surjective f := by
    intro y
    have hy : y.val * c = c * y.val := Subgroup.mem_centralizer_singleton_iff.mp y.property
    have hymat : (y.val : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F)
        = (c : Matrix (Fin 2) (Fin 2) F) * (y.val : Matrix (Fin 2) (Fin 2) F) := by
      have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
        (z : Matrix (Fin 2) (Fin 2) F)) hy
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using h
    obtain ⟨p, q, hpq⟩ := (matrix_centralizer_eq_span hcsq hroot _).mp hymat
    have hdet : p ^ 2 + p * q + q ^ 2 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe y.val
      rw [hpq, det_smul_one_add_smul, htrc, hdetc] at h
      simpa only [mul_one] using h
    refine ⟨⟨(p, q), hdet⟩, ?_⟩
    exact Subtype.ext (Subtype.ext hpq.symm)
  -- Compare cardinalities.
  have hcard : Nat.card ↥(Subgroup.centralizer ({c} : Set (Matrix.SpecialLinearGroup (Fin 2) F)))
      = Nat.card {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} :=
    Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm
  rw [hcard, norm_form_card hroot, hF]

end Work.ThmF.ChV12
