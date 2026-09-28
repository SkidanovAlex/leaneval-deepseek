import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.SigmaDefs
import Submission.Work.HP.Vero.span_realify_latOrth_inf
import Submission.Work.HP.PairsAux
import Submission.Work.HP.Lat.detLAux

/-!
# Definitions for the two-vector successive-minima bound `GamTwo_dual_lam1`

Browning–Le Boudec–Sawin (Annals 197 (3) 2023) §3.2–3.3 study, for primitive `ℤ`-linearly
independent `x, y ∈ ℤ^{n+1}` (and `d ≥ 2`),

* `𝓠₂(x,y) = (ℝν₂(x) ⊕ ℝν₂(y)) ∩ ℤ^{N₂ₙ}` and
  `𝓠₃(x,y) = (ℝν₂(x) ⊕ ℝν₂(y) ⊕ ℝν₂(x+y)) ∩ ℤ^{N₂ₙ}`, both primitive (saturated);
* `ℒ(x,y) = (ℝx ⊕ ℝy) ∩ ℤ^{n+1}`;
* the row map `rᵢ(c)_j = c(XᵢXⱼ)`;
* the gcd `𝒢₃` of the `3 × 3` minors of three columns.

We realise `𝓠₂`, `𝓠₃`, `ℒ` as `satSpan`, the saturation of a set of integer vectors, i.e. the
preimage under `intCastPi : (ι → ℤ) → (ι → ℝ)` of the real span of the set (`mem_satSpan`), which is
manifestly saturated (`isSat_satSpan`) and has the same real span (`span_intCast_satSpan`).

We also introduce `perpComp`, the "perpendicular component" with respect to the real span of an
integral lattice, defined through the inverse Gram matrix of a `ℤ`-basis (the plain function type
`ι → ℝ` carries no `InnerProductSpace` instance for the standard Euclidean form, so the projection
is built by hand).
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP.Sig2

open Work.HP Finset

/-! ## The saturation of a set of integer vectors -/

/-- The saturation of a set `S` of integer vectors: the integer vectors in the real span of `S`. -/
noncomputable def satSpan {ι : Type*} [Fintype ι] (S : Set (ι → ℤ)) : Submodule ℤ (ι → ℤ) :=
  Submodule.comap intCastPi
    ((Submodule.span ℝ (intCastPi '' S)).restrictScalars ℤ)

@[simp] theorem mem_satSpan {ι : Type*} [Fintype ι] {S : Set (ι → ℤ)} {b : ι → ℤ} :
    b ∈ satSpan S ↔ intCastPi b ∈ Submodule.span ℝ (intCastPi '' S) := Iff.rfl

/-- The saturation of a set of integer vectors is saturated. -/
theorem isSat_satSpan {ι : Type*} [Fintype ι] (S : Set (ι → ℤ)) :
    IsSat (satSpan S) := by
  intro v ⟨m, hm, hmem⟩
  rw [mem_satSpan] at hmem ⊢
  have h1 : intCastPi (m • v) = (m : ℝ) • intCastPi v := by
    rw [map_smul, Int.cast_smul_eq_zsmul]
  have hmR : ((m : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have h2 : intCastPi v = ((m : ℝ))⁻¹ • intCastPi (m • v) := by
    rw [h1, smul_smul, inv_mul_cancel₀ hmR, one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ hmem

/-- The real span of the saturation of `S` is the real span of `S`. -/
theorem span_intCast_satSpan {ι : Type*} [Fintype ι] (S : Set (ι → ℤ)) :
    Submodule.span ℝ (intCastPi '' (satSpan S : Set (ι → ℤ)))
      = Submodule.span ℝ (intCastPi '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨b, hb, rfl⟩
    exact hb
  · rw [Submodule.span_le]
    rintro y ⟨b, hb, rfl⟩
    exact Submodule.subset_span ⟨b, mem_satSpan.mpr (Submodule.subset_span ⟨b, hb, rfl⟩), rfl⟩

/-- The real span of the realification of `{a, b}` is the real span of the two realifications. -/
theorem span_intCast_pair {ι : Type*} [Fintype ι] (a b : ι → ℤ) :
    Submodule.span ℝ (intCastPi '' ({a, b} : Set (ι → ℤ)))
      = Submodule.span ℝ ({intCastPi a, intCastPi b} : Set (ι → ℝ)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨z, hz, rfl⟩
    rcases hz with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · rw [Submodule.span_le]
    rintro y hy
    rcases hy with rfl | rfl
    · exact Submodule.subset_span ⟨a, by simp, rfl⟩
    · exact Submodule.subset_span ⟨b, by simp, rfl⟩

theorem span_intCast_triple {ι : Type*} [Fintype ι] (a b c : ι → ℤ) :
    Submodule.span ℝ (intCastPi '' ({a, b, c} : Set (ι → ℤ)))
      = Submodule.span ℝ ({intCastPi a, intCastPi b, intCastPi c} : Set (ι → ℝ)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨z, hz, rfl⟩
    rcases hz with rfl | rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · rw [Submodule.span_le]
    rintro y hy
    rcases hy with rfl | rfl | rfl
    · exact Submodule.subset_span ⟨a, by simp, rfl⟩
    · exact Submodule.subset_span ⟨b, by simp, rfl⟩
    · exact Submodule.subset_span ⟨c, by simp, rfl⟩

/-- `toR` and `intCastPi` are the same map. -/
lemma toR_eq_intCastPi {ι : Type*} [Fintype ι] (v : ι → ℤ) : toR v = intCastPi v := rfl

/-! ## The lattices `𝓠₂`, `𝓠₃`, the real spans `V₂, V₃` and `ℒ` -/

/-- `𝓠₂(x,y) = (ℝν₂(x) ⊕ ℝν₂(y)) ∩ ℤ^{N₂ₙ}`. -/
noncomputable def Q2 (n : ℕ) (x y : Fin (n + 1) → ℤ) : Submodule ℤ (Mon 2 n → ℤ) :=
  satSpan ({veronese 2 n x, veronese 2 n y} : Set (Mon 2 n → ℤ))

/-- `𝓠₃(x,y) = (ℝν₂(x) ⊕ ℝν₂(y) ⊕ ℝν₂(x+y)) ∩ ℤ^{N₂ₙ}`. -/
noncomputable def Q3 (n : ℕ) (x y : Fin (n + 1) → ℤ) : Submodule ℤ (Mon 2 n → ℤ) :=
  satSpan ({veronese 2 n x, veronese 2 n y, veronese 2 n (x + y)} : Set (Mon 2 n → ℤ))

/-- `V₂ = span_ℝ {ν₂(x), ν₂(y)} ⊆ ℝ^{N₂ₙ}`. -/
noncomputable def V2R (n : ℕ) (x y : Fin (n + 1) → ℤ) : Submodule ℝ (Mon 2 n → ℝ) :=
  Submodule.span ℝ ({toR (veronese 2 n x), toR (veronese 2 n y)} : Set (Mon 2 n → ℝ))

/-- `V₃ = span_ℝ {ν₂(x), ν₂(y), ν₂(x+y)} ⊆ ℝ^{N₂ₙ}`. -/
noncomputable def V3R (n : ℕ) (x y : Fin (n + 1) → ℤ) : Submodule ℝ (Mon 2 n → ℝ) :=
  Submodule.span ℝ ({toR (veronese 2 n x), toR (veronese 2 n y),
    toR (veronese 2 n (x + y))} : Set (Mon 2 n → ℝ))

/-- `ℒ(x,y) = (ℝx ⊕ ℝy) ∩ ℤ^{n+1}`. -/
noncomputable def Lxy (n : ℕ) (x y : Fin (n + 1) → ℤ) : Submodule ℤ (Fin (n + 1) → ℤ) :=
  satSpan ({x, y} : Set (Fin (n + 1) → ℤ))

theorem isSat_Q2 (n : ℕ) (x y : Fin (n + 1) → ℤ) : IsSat (Q2 n x y) := isSat_satSpan _

theorem isSat_Q3 (n : ℕ) (x y : Fin (n + 1) → ℤ) : IsSat (Q3 n x y) := isSat_satSpan _

theorem isSat_Lxy (n : ℕ) (x y : Fin (n + 1) → ℤ) : IsSat (Lxy n x y) := isSat_satSpan _

/-- `b ∈ 𝓠₂` iff its realification lies in `V₂`. -/
theorem mem_Q2_iff (n : ℕ) (x y : Fin (n + 1) → ℤ) (b : Mon 2 n → ℤ) :
    b ∈ Q2 n x y ↔ toR b ∈ V2R n x y := by
  rw [Q2, mem_satSpan, span_intCast_pair, V2R]
  exact Iff.rfl

/-- `b ∈ 𝓠₃` iff its realification lies in `V₃`. -/
theorem mem_Q3_iff (n : ℕ) (x y : Fin (n + 1) → ℤ) (b : Mon 2 n → ℤ) :
    b ∈ Q3 n x y ↔ toR b ∈ V3R n x y := by
  rw [Q3, mem_satSpan, span_intCast_triple, V3R]
  exact Iff.rfl

/-- `b ∈ ℒ(x,y)` iff its realification lies in `span_ℝ {toR x, toR y}`. -/
theorem mem_Lxy_iff (n : ℕ) (x y : Fin (n + 1) → ℤ) (b : Fin (n + 1) → ℤ) :
    b ∈ Lxy n x y ↔ toR b ∈ Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ)) := by
  rw [Lxy, mem_satSpan, span_intCast_pair]
  exact Iff.rfl

/-- The real span of `ℒ(x,y)` is `span_ℝ {toR x, toR y}`. -/
theorem span_intCast_Lxy (n : ℕ) (x y : Fin (n + 1) → ℤ) :
    Submodule.span ℝ (intCastPi '' (Lxy n x y : Set (Fin (n + 1) → ℤ)))
      = Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ)) := by
  rw [show Lxy n x y = satSpan ({x, y} : Set (Fin (n + 1) → ℤ)) from rfl,
    span_intCast_satSpan, span_intCast_pair]
  rfl

/-- The real span of `𝓠₂` is `V₂`. -/
theorem span_intCast_Q2 (n : ℕ) (x y : Fin (n + 1) → ℤ) :
    Submodule.span ℝ (intCastPi '' (Q2 n x y : Set (Mon 2 n → ℤ))) = V2R n x y := by
  rw [show Q2 n x y = satSpan ({veronese 2 n x, veronese 2 n y} : Set (Mon 2 n → ℤ)) from rfl,
    span_intCast_satSpan, span_intCast_pair, V2R]
  rfl

/-- The real span of `𝓠₃` is `V₃`. -/
theorem span_intCast_Q3 (n : ℕ) (x y : Fin (n + 1) → ℤ) :
    Submodule.span ℝ (intCastPi '' (Q3 n x y : Set (Mon 2 n → ℤ))) = V3R n x y := by
  rw [show Q3 n x y = satSpan ({veronese 2 n x, veronese 2 n y, veronese 2 n (x + y)} :
      Set (Mon 2 n → ℤ)) from rfl, span_intCast_satSpan, span_intCast_triple, V3R]
  rfl

/-- `𝓠₂ ⊆ 𝓠₃`. -/
theorem Q2_le_Q3 (n : ℕ) (x y : Fin (n + 1) → ℤ) : Q2 n x y ≤ Q3 n x y := by
  intro b hb
  rw [mem_Q2_iff] at hb
  rw [mem_Q3_iff]
  exact Submodule.span_mono (by
    rintro z (rfl | rfl) <;> simp) hb

/-! ## The row map `rᵢ` on real coefficient vectors -/

/-- The exponent vector of `Xᵢ Xⱼ` has `r`-th coordinate `1_{r=i} + 1_{r=j}`. -/
lemma pairMon_val_eq (n : ℕ) (i j r : Fin (n + 1)) :
    ((Vero.pairMon n i j).1 r).val
      = (if r = i then 1 else 0) + (if r = j then 1 else 0) := by
  simp only [Vero.pairMon, Work.HP.NA.monDij]

/-- The row map `j ↦ XᵢXⱼ` on monomials is injective. -/
lemma pairMon_injective_right (n : ℕ) (i : Fin (n + 1)) :
    Function.Injective (fun j : Fin (n + 1) => Vero.pairMon n i j) := by
  intro j j' h
  have hv : ((Vero.pairMon n i j).1 j).val = ((Vero.pairMon n i j').1 j).val :=
    congrArg (fun (z : Mon 2 n) => (z.1 j).val) h
  rw [pairMon_val_eq, pairMon_val_eq] at hv
  have hkey : (if j = j' then (1 : ℕ) else 0) = 1 := by
    by_cases hji : j = i
    · rw [if_pos hji, if_pos rfl] at hv
      by_cases hjj : j = j'
      · simp [hjj]
      · rw [if_neg hjj] at hv
        omega
    · rw [if_neg hji, if_pos rfl] at hv
      by_cases hjj : j = j'
      · simp [hjj]
      · rw [if_neg hjj] at hv
        omega
  by_cases hjj : j = j'
  · exact hjj
  · rw [if_neg hjj] at hkey
    exact absurd hkey (by norm_num)

/-- The real row vector `rᵢ(a)`, `(rᵢ a)_j = a (Xᵢ Xⱼ)`. -/
def rowVecR (n : ℕ) (i : Fin (n + 1)) (c : Mon 2 n → ℝ) : Fin (n + 1) → ℝ :=
  fun j => c (Vero.pairMon n i j)

@[simp] lemma rowVecR_apply (n : ℕ) (i : Fin (n + 1)) (c : Mon 2 n → ℝ) (j : Fin (n + 1)) :
    rowVecR n i c j = c (Vero.pairMon n i j) := rfl

lemma rowVecR_add (n : ℕ) (i : Fin (n + 1)) (c d : Mon 2 n → ℝ) :
    rowVecR n i (c + d) = rowVecR n i c + rowVecR n i d := by
  ext j; simp [rowVecR]

lemma rowVecR_smul (n : ℕ) (i : Fin (n + 1)) (a : ℝ) (c : Mon 2 n → ℝ) :
    rowVecR n i (a • c) = a • rowVecR n i c := by
  ext j; simp [rowVecR]

lemma rowVecR_sub (n : ℕ) (i : Fin (n + 1)) (c d : Mon 2 n → ℝ) :
    rowVecR n i (c - d) = rowVecR n i c - rowVecR n i d := by
  ext j; simp [rowVecR]

/-- The norm of the row vector `rᵢ(a)` is at most that of `a`. -/
theorem rNorm_rowVecR_le (n : ℕ) (i : Fin (n + 1)) (c : Mon 2 n → ℝ) :
    rNorm (rowVecR n i c) ≤ rNorm c := by
  have hinj : ∀ a ∈ (Finset.univ : Finset (Fin (n + 1))),
      ∀ b ∈ (Finset.univ : Finset (Fin (n + 1))),
      Vero.pairMon n i a = Vero.pairMon n i b → a = b :=
    fun a _ b _ h => pairMon_injective_right n i h
  have h1 : (∑ j : Fin (n + 1), (rowVecR n i c j) ^ 2)
      = ∑ m ∈ (Finset.univ.image fun j : Fin (n + 1) => Vero.pairMon n i j), (c m) ^ 2 := by
    rw [Finset.sum_image hinj]
    rfl
  have h2 : (∑ m ∈ (Finset.univ.image fun j : Fin (n + 1) => Vero.pairMon n i j), (c m) ^ 2)
      ≤ ∑ m : Mon 2 n, (c m) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun m _ _ => sq_nonneg (c m))
  rw [rNorm, rNorm]
  apply Real.sqrt_le_sqrt
  rw [h1]
  exact h2

/-! ## The gcd of the `3 × 3` minors -/

/-- The gcd of the `3 × 3` minors of the three columns `c₁, c₂, c₃`. -/
def gcd3 {ι : Type*} [Fintype ι] (c₁ c₂ c₃ : ι → ℤ) : ℤ :=
  Finset.univ.gcd (fun p : Fin 3 → ι =>
    Matrix.det (Matrix.of fun i j : Fin 3 => ![c₁, c₂, c₃] j (p i)))

/-! ## The perpendicular component with respect to the span of an integral lattice -/

/-- The real Gram matrix of a `ℤ`-basis `b` of `Λ`. -/
noncomputable def gramOf {ι κ : Type*} [Fintype ι] [Fintype κ] {Λ : Submodule ℤ (ι → ℤ)}
    (b : Module.Basis κ ℤ Λ) : Matrix κ κ ℝ :=
  Matrix.of fun i j => ∑ x, (((b i : Λ) : ι → ℤ) x : ℝ) * (((b j : Λ) : ι → ℤ) x : ℝ)

/-- The perpendicular component of `w ∈ ℝ^ι` with respect to `span_ℝ(Λ)`, computed with the inverse
Gram matrix of the `ℤ`-basis `b` of `Λ`. -/
noncomputable def perpCompB {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {Λ : Submodule ℤ (ι → ℤ)} (b : Module.Basis κ ℤ Λ) (w : ι → ℝ) : ι → ℝ :=
  w - ∑ i : κ, (∑ j : κ, (gramOf b)⁻¹ i j * dotR w (intCastPi (((b j : Λ) : ι → ℤ))))
      • intCastPi (((b i : Λ) : ι → ℤ))

/-- The perpendicular component of `w ∈ ℝ^ι` with respect to `span_ℝ(Λ)`. -/
noncomputable def perpComp {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (ι → ℤ))
    (w : ι → ℝ) : ι → ℝ :=
  perpCompB (Submodule.basisOfPid (Pi.basisFun ℤ ι) Λ).2 w

end Work.HP.Sig2
