import Mathlib
import Submission.Work.ConvexCells.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.ConvexCells

open scoped BigOperators

/-! ### The integral certificates in real form

The certificates stored in `PolytopeData` are integral: they are identities and inequalities for the
integer normals `P.nrm` and right hand sides `P.rhs`.  Since `P.nR i = D⁻¹ • toE (P.nrm i)` and
`P.bR i = (P.rhs i)/D`, an integral identity translates into a real identity in the ambient space.
The lemmas below make this translation explicit. -/

/-- `toE` of the integral normal is `D` times the real normal. -/
theorem toE_nrm {d : ℕ} (P : PolytopeData d) (h : P.Ok) (t : Fin P.m) :
    toE (P.nrm t) = (P.D : ℝ) • P.nR t := by
  have hD : (P.D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (PolytopeData.Ok.D_pos P h))
  rw [PolytopeData.nR, smul_smul, mul_inv_cancel₀ hD, one_smul]

/-- Real form of the emptiness certificate: the integral combination of normals of
`Ok.emp_cert` is the zero vector, so the same combination of the real normals vanishes. -/
theorem toE_comb {d : ℕ} (P : PolytopeData d) (h : P.Ok) (s : Finset (Fin P.m)) (i : Fin P.m)
    (A : Fin P.m → ℤ) (I : ℤ) (G : Fin P.m → ℤ) :
    toE ((∑ k ∈ s, A k • P.nrm k) + I • P.nrm i - ∑ l, G l • P.nrm l)
      = (P.D : ℝ) • ((∑ k ∈ s, (A k : ℝ) • P.nR k) + (I : ℝ) • P.nR i
          - ∑ l, (G l : ℝ) • P.nR l) := by
  have hD : (P.D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (PolytopeData.Ok.D_pos P h))
  have htr : ∀ t : Fin P.m, toE (P.nrm t) = (P.D : ℝ) • P.nR t := toE_nrm P h
  rw [toE_sub, toE_add, toE_sum, toE_sum (Finset.univ), toE_smul]
  simp only [toE_smul, htr]
  rw [smul_sub, smul_add, Finset.smul_sum, Finset.smul_sum]
  simp only [smul_smul, mul_comm]

/-- Real form of the adding-constraint certificate. -/
theorem toE_comb_add {d : ℕ} (P : PolytopeData d) (h : P.Ok) (s : Finset (Fin P.m))
    (i j : Fin P.m) (A : Fin P.m → ℤ) (I : ℤ) (G : Fin P.m → ℤ) (D0 : ℤ) :
    toE (D0 • P.nrm j - ((∑ k ∈ s, A k • P.nrm k) + I • P.nrm i) + ∑ l, G l • P.nrm l)
      = (P.D : ℝ) • ((D0 : ℝ) • P.nR j - ((∑ k ∈ s, (A k : ℝ) • P.nR k) + (I : ℝ) • P.nR i)
          + ∑ l, (G l : ℝ) • P.nR l) := by
  have hD : (P.D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (PolytopeData.Ok.D_pos P h))
  have htr : ∀ t : Fin P.m, toE (P.nrm t) = (P.D : ℝ) • P.nR t := toE_nrm P h
  rw [toE_add, toE_sub, toE_add, toE_sum, toE_sum (Finset.univ), toE_smul, toE_smul]
  simp only [toE_smul, htr]
  simp only [smul_add, smul_sub, Finset.smul_sum, smul_smul, mul_comm]

/-- The scalar identity behind the emptiness certificate: the combination of the inner products
`⟪nR k, x⟫` with the coefficients of `Ok.emp_cert` vanishes. -/
theorem emp_zero {d : ℕ} (P : PolytopeData d) (h : P.Ok) (f : Fin P.K) (i : Fin P.m)
    (hsel : P.empSel f i = true) (x : E d) :
    ∑ k ∈ P.tight f, (P.empA f i k : ℝ) * inner ℝ (P.nR k) x
      + (P.empI f i : ℝ) * inner ℝ (P.nR i) x
      - ∑ l, (P.empG f i l : ℝ) * inner ℝ (P.nR l) x = 0 := by
  obtain ⟨hG, hvec, hnum⟩ := PolytopeData.Ok.emp_cert P h f i hsel
  have hD : (P.D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (PolytopeData.Ok.D_pos P h))
  have hV0 : ((∑ k ∈ P.tight f, P.empA f i k • P.nrm k) + P.empI f i • P.nrm i
      - ∑ l, P.empG f i l • P.nrm l : Fin d → ℤ) = 0 := by
    funext j'
    simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    exact hvec j'
  have htoE0 : toE ((∑ k ∈ P.tight f, P.empA f i k • P.nrm k) + P.empI f i • P.nrm i
      - ∑ l, P.empG f i l • P.nrm l) = 0 := by rw [hV0, toE_zero]
  have hDmul : (P.D : ℝ) • ((∑ k ∈ P.tight f, (P.empA f i k : ℝ) • P.nR k)
      + (P.empI f i : ℝ) • P.nR i - ∑ l, (P.empG f i l : ℝ) • P.nR l) = 0 := by
    rw [← toE_comb P h (P.tight f) i (P.empA f i) (P.empI f i) (P.empG f i)]
    exact htoE0
  have hinner : inner ℝ ((∑ k ∈ P.tight f, (P.empA f i k : ℝ) • P.nR k)
      + (P.empI f i : ℝ) • P.nR i - ∑ l, (P.empG f i l : ℝ) • P.nR l) x = 0 := by
    have h1 : (P.D : ℝ) * inner ℝ ((∑ k ∈ P.tight f, (P.empA f i k : ℝ) • P.nR k)
        + (P.empI f i : ℝ) • P.nR i - ∑ l, (P.empG f i l : ℝ) • P.nR l) x = 0 := by
      have h2 := congrArg (fun w : E d => inner ℝ w x) hDmul
      rw [inner_smul_left, RCLike.conj_to_real] at h2
      simpa using h2
    exact (mul_eq_zero.mp h1).resolve_left hD
  rw [← hinner, inner_sub_left, inner_add_left,
    PolytopeData.inner_lincomb_left (P.tight f) (fun k => (P.empA f i k : ℝ))
      (fun k : Fin P.m => P.nR k) x,
    inner_smul_left, RCLike.conj_to_real,
    PolytopeData.inner_lincomb_left Finset.univ (fun l => (P.empG f i l : ℝ))
      (fun l : Fin P.m => P.nR l) x]

/-- If `empSel f i = true`, the region `Fset f ∩ {n_i = b_i}` is empty: no point of the polytope can
be tight at both `f` and `i`. -/
theorem emp_contra {d : ℕ} (P : PolytopeData d) (h : P.Ok) (f : Fin P.K) (i : Fin P.m)
    (hsel : P.empSel f i = true) {x : E d} (hx : x ∈ P.Pset)
    (hf : ∀ k ∈ P.tight f, inner ℝ (P.nR k) x = P.bR k)
    (hi : inner ℝ (P.nR i) x = P.bR i) : False := by
  obtain ⟨hG, hvec, hnum⟩ := PolytopeData.Ok.emp_cert P h f i hsel
  have hDpos : (0:ℝ) < (P.D:ℝ) := by exact_mod_cast PolytopeData.Ok.D_pos P h
  have hDne : (P.D:ℝ) ≠ 0 := ne_of_gt hDpos
  have hzero := emp_zero P h f i hsel x
  have hle : ∑ k ∈ P.tight f, (P.empA f i k : ℝ) * P.bR k
      + (P.empI f i : ℝ) * P.bR i - ∑ l, (P.empG f i l : ℝ) * P.bR l ≤ 0 := by
    have hZle : ∑ l, (P.empG f i l : ℝ) * inner ℝ (P.nR l) x
        ≤ ∑ l, (P.empG f i l : ℝ) * P.bR l :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hx l) (by exact_mod_cast hG l)
    have hXeq : ∑ k ∈ P.tight f, (P.empA f i k : ℝ) * inner ℝ (P.nR k) x
        = ∑ k ∈ P.tight f, (P.empA f i k : ℝ) * P.bR k :=
      Finset.sum_congr rfl fun k hk => by rw [hf k hk]
    have hIeq : (P.empI f i : ℝ) * inner ℝ (P.nR i) x = (P.empI f i : ℝ) * P.bR i := by rw [hi]
    linarith [hzero, hZle, hXeq, hIeq]
  have hpos : 0 < ∑ k ∈ P.tight f, (P.empA f i k : ℝ) * P.bR k
      + (P.empI f i : ℝ) * P.bR i - ∑ l, (P.empG f i l : ℝ) * P.bR l := by
    have h1 : (0:ℝ) < (((∑ k ∈ P.tight f, P.empA f i k * P.rhs k) + P.empI f i * P.rhs i
        - ∑ l, P.empG f i l * P.rhs l : ℤ) : ℝ) := by exact_mod_cast hnum
    have hsumA : ∑ k ∈ P.tight f, (P.empA f i k : ℝ) * P.bR k
        = (∑ k ∈ P.tight f, (P.empA f i k : ℝ) * (P.rhs k : ℝ)) / (P.D : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by rw [PolytopeData.bR, mul_div_assoc]
    have hsumG : ∑ l, (P.empG f i l : ℝ) * P.bR l
        = (∑ l, (P.empG f i l : ℝ) * (P.rhs l : ℝ)) / (P.D : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun l _ => by rw [PolytopeData.bR, mul_div_assoc]
    have hI : (P.empI f i : ℝ) * P.bR i = (P.empI f i : ℝ) * (P.rhs i : ℝ) / (P.D : ℝ) := by
      rw [PolytopeData.bR, mul_div_assoc]
    have hcast : (((∑ k ∈ P.tight f, P.empA f i k * P.rhs k) + P.empI f i * P.rhs i
        - ∑ l, P.empG f i l * P.rhs l : ℤ) : ℝ)
        = ((∑ k ∈ P.tight f, (P.empA f i k : ℝ) * P.bR k)
            + (P.empI f i : ℝ) * P.bR i - ∑ l, (P.empG f i l : ℝ) * P.bR l) * (P.D : ℝ) := by
      rw [hsumA, hsumG, hI, ← add_div, ← sub_div, div_mul_cancel₀ _ hDne]
      push_cast
      ring
    rw [hcast] at h1
    nlinarith [h1, hDpos]
  linarith

/-- The scalar identity behind the adding-constraint certificate. -/
theorem add_zero {d : ℕ} (P : PolytopeData d) (h : P.Ok) (f : Fin P.K) (i j : Fin P.m)
    (hsel : P.empSel f i = false) (hj : j ∈ P.tight (P.addF f i)) (y : E d) :
    (P.addD f i j : ℝ) * inner ℝ (P.nR j) y
      - ((∑ k ∈ P.tight f, (P.addA f i j k : ℝ) * inner ℝ (P.nR k) y)
          + (P.addI f i j : ℝ) * inner ℝ (P.nR i) y)
      + ∑ l, (P.addG f i j l : ℝ) * inner ℝ (P.nR l) y = 0 := by
  obtain ⟨hsub, hD0pos, hG0, hvec, hnum⟩ := PolytopeData.Ok.add_cert P h f i hsel
  have hD : (P.D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (PolytopeData.Ok.D_pos P h))
  have hvecj := hvec j hj
  have hV0 : ((P.addD f i j • P.nrm j) - ((∑ k ∈ P.tight f, P.addA f i j k • P.nrm k)
      + P.addI f i j • P.nrm i) + ∑ l, P.addG f i j l • P.nrm l : Fin d → ℤ) = 0 := by
    funext j'
    simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    exact hvecj j'
  have htoE0 : toE ((P.addD f i j • P.nrm j) - ((∑ k ∈ P.tight f, P.addA f i j k • P.nrm k)
      + P.addI f i j • P.nrm i) + ∑ l, P.addG f i j l • P.nrm l) = 0 := by
    rw [hV0, toE_zero]
  have hDmul : (P.D : ℝ) • ((P.addD f i j : ℝ) • P.nR j
      - ((∑ k ∈ P.tight f, (P.addA f i j k : ℝ) • P.nR k) + (P.addI f i j : ℝ) • P.nR i)
      + ∑ l, (P.addG f i j l : ℝ) • P.nR l) = 0 := by
    rw [← toE_comb_add P h (P.tight f) i j (P.addA f i j) (P.addI f i j) (P.addG f i j)
      (P.addD f i j)]
    exact htoE0
  have hZeq : inner ℝ ((P.addD f i j : ℝ) • P.nR j
      - ((∑ k ∈ P.tight f, (P.addA f i j k : ℝ) • P.nR k) + (P.addI f i j : ℝ) • P.nR i)
      + ∑ l, (P.addG f i j l : ℝ) • P.nR l) y = 0 := by
    have h1 : (P.D : ℝ) * inner ℝ ((P.addD f i j : ℝ) • P.nR j
        - ((∑ k ∈ P.tight f, (P.addA f i j k : ℝ) • P.nR k) + (P.addI f i j : ℝ) • P.nR i)
        + ∑ l, (P.addG f i j l : ℝ) • P.nR l) y = 0 := by
      have h2 := congrArg (fun w : E d => inner ℝ w y) hDmul
      rw [inner_smul_left, RCLike.conj_to_real] at h2
      simpa using h2
    exact (mul_eq_zero.mp h1).resolve_left hD
  rw [← hZeq, inner_add_left, inner_sub_left, inner_add_left, inner_smul_left,
    RCLike.conj_to_real,
    PolytopeData.inner_lincomb_left (P.tight f) (fun k => (P.addA f i j k : ℝ))
      (fun k : Fin P.m => P.nR k) y,
    inner_smul_left, RCLike.conj_to_real,
    PolytopeData.inner_lincomb_left Finset.univ (fun l => (P.addG f i j l : ℝ))
      (fun l : Fin P.m => P.nR l) y]

/-- The adding-constraint certificate, used: on the region where the face `f` is tight and the
constraint `i` is tight, every constraint of the tight set of `addF f i` is tight as well. -/
theorem add_cert_imp {d : ℕ} (P : PolytopeData d) (h : P.Ok) (f : Fin P.K) (i : Fin P.m)
    (hsel : P.empSel f i = false) {y : E d} (hy : y ∈ P.Pset)
    (hf : ∀ k ∈ P.tight f, inner ℝ (P.nR k) y = P.bR k)
    (hi : inner ℝ (P.nR i) y = P.bR i) :
    ∀ j ∈ P.tight (P.addF f i), inner ℝ (P.nR j) y = P.bR j := by
  intro j hj
  have hDpos : (0:ℝ) < (P.D:ℝ) := by exact_mod_cast PolytopeData.Ok.D_pos P h
  have hDne : (P.D:ℝ) ≠ 0 := ne_of_gt hDpos
  have hzero := add_zero P h f i j hsel hj y
  obtain ⟨hsub, hD0pos, hG0, hvec, hnum⟩ := PolytopeData.Ok.add_cert P h f i hsel
  have hle : (P.addD f i j : ℝ) * P.bR j
      - ((∑ k ∈ P.tight f, (P.addA f i j k : ℝ) * P.bR k) + (P.addI f i j : ℝ) * P.bR i)
      + ∑ l, (P.addG f i j l : ℝ) * P.bR l ≤ 0 := by
    have hn := hnum j hj
    have h1 : ((((P.addD f i j * P.rhs j)
        - ((∑ k ∈ P.tight f, P.addA f i j k * P.rhs k) + P.addI f i j * P.rhs i)
        + ∑ l, P.addG f i j l * P.rhs l : ℤ) : ℝ)) ≤ 0 := by exact_mod_cast hn
    have hsumA : ∑ k ∈ P.tight f, (P.addA f i j k : ℝ) * P.bR k
        = (∑ k ∈ P.tight f, (P.addA f i j k : ℝ) * (P.rhs k : ℝ)) / (P.D : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by rw [PolytopeData.bR, mul_div_assoc]
    have hsumG : ∑ l, (P.addG f i j l : ℝ) * P.bR l
        = (∑ l, (P.addG f i j l : ℝ) * (P.rhs l : ℝ)) / (P.D : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun l _ => by rw [PolytopeData.bR, mul_div_assoc]
    have hIj : (P.addI f i j : ℝ) * P.bR i = (P.addI f i j : ℝ) * (P.rhs i : ℝ) / (P.D : ℝ) := by
      rw [PolytopeData.bR, mul_div_assoc]
    have hDj : (P.addD f i j : ℝ) * P.bR j = (P.addD f i j : ℝ) * (P.rhs j : ℝ) / (P.D : ℝ) := by
      rw [PolytopeData.bR, mul_div_assoc]
    have hcast : ((((P.addD f i j * P.rhs j)
        - ((∑ k ∈ P.tight f, P.addA f i j k * P.rhs k) + P.addI f i j * P.rhs i)
        + ∑ l, P.addG f i j l * P.rhs l : ℤ) : ℝ))
        = ((P.addD f i j : ℝ) * P.bR j
            - ((∑ k ∈ P.tight f, (P.addA f i j k : ℝ) * P.bR k) + (P.addI f i j : ℝ) * P.bR i)
            + ∑ l, (P.addG f i j l : ℝ) * P.bR l) * (P.D : ℝ) := by
      rw [hDj, hsumA, hsumG, hIj, ← add_div, ← sub_div, ← add_div,
        div_mul_cancel₀ _ hDne]
      push_cast
      ring
    rw [hcast] at h1
    nlinarith [h1, hDpos]
  have hD0R : (0:ℝ) < (P.addD f i j : ℝ) := by exact_mod_cast hD0pos j hj
  have hGli : ∀ l, (0:ℝ) ≤ (P.addG f i j l : ℝ) := fun l => by exact_mod_cast hG0 j hj l
  have hZle : ∑ l, (P.addG f i j l : ℝ) * inner ℝ (P.nR l) y
      ≤ ∑ l, (P.addG f i j l : ℝ) * P.bR l :=
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hy l) (hGli l)
  have hXeq : ∑ k ∈ P.tight f, (P.addA f i j k : ℝ) * inner ℝ (P.nR k) y
      = ∑ k ∈ P.tight f, (P.addA f i j k : ℝ) * P.bR k :=
    Finset.sum_congr rfl fun k hk => by rw [hf k hk]
  have hIeq : (P.addI f i j : ℝ) * inner ℝ (P.nR i) y = (P.addI f i j : ℝ) * P.bR i := by rw [hi]
  have hkey : (P.addD f i j : ℝ) * P.bR j ≤ (P.addD f i j : ℝ) * inner ℝ (P.nR j) y := by
    linarith [hzero, hle, hZle, hXeq, hIeq]
  exact le_antisymm (hy j) (le_of_mul_le_mul_left hkey hD0R)

/-- The decidable checks imply face completeness: every point of the polytope has its tight set among
the listed faces.

Proof: let `A = P.tightAt x`.  The finite set `{f | P.tight f ⊆ A}` is nonempty (`P.top`, since
`Ok.tight_top` gives `tight top = ∅`); take `f` maximal in it.  If `tight f ⊊ A`, pick
`i ∈ A \ tight f`; then `x` lies in the region `Fset f ∩ {n_i = b_i}` (using `hf` and
`P.tightAt_of_mem`/`P.mem_tightAt_iff`), so `P.empSel f i = true` is impossible by `Ok.emp_cert`,
and `addF_imp` plus `Ok.add_cert`'s `tight f ∪ {i} ⊆ tight (addF f i)` produce a listed face with
tight set strictly between `tight f` and `A`, contradicting maximality.  Hence `tight f = A`. -/
theorem Carriers_of_Ok {d : ℕ} (P : PolytopeData d) (h : P.Ok) : P.Carriers := by
  classical
  intro x hx
  -- any proper sub-face of the carrier can be strictly enlarged inside the carrier
  have key : ∀ f : Fin P.K, P.tight f ⊆ P.tightAt x → P.tight f ≠ P.tightAt x →
      ∃ g : Fin P.K, P.tight f ⊂ P.tight g ∧ P.tight g ⊆ P.tightAt x := by
    intro f hf hne
    have hssub : P.tight f ⊂ P.tightAt x := Finset.ssubset_iff_subset_ne.mpr ⟨hf, hne⟩
    obtain ⟨i, hiA, hi_not⟩ := Finset.exists_of_ssubset hssub
    have hlin : ∀ k ∈ P.tight f, inner ℝ (P.nR k) x = P.bR k :=
      fun k hk => (PolytopeData.tightAt_of_mem P hx k).mp (hf hk)
    have hii : inner ℝ (P.nR i) x = P.bR i := (PolytopeData.tightAt_of_mem P hx i).mp hiA
    have hsel : P.empSel f i = false := by
      cases hb : P.empSel f i with
      | false => rfl
      | true => exact (emp_contra P h f i hb hx hlin hii).elim
    refine ⟨P.addF f i, ?_, ?_⟩
    · have hsub := (PolytopeData.Ok.add_cert P h f i hsel).1
      have hi_mem : i ∈ P.tight (P.addF f i) :=
        hsub (Finset.mem_union_right _ (Finset.mem_singleton_self i))
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left.trans hsub, ?_⟩
      intro hcontra
      rw [← hcontra] at hi_mem
      exact hi_not hi_mem
    · intro k hk
      rw [PolytopeData.tightAt_of_mem P hx k]
      exact add_cert_imp P h f i hsel hx hlin hii k hk
  -- take a face of maximal cardinality among those whose tight set lies in the carrier
  obtain ⟨f, hfS, hfmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun f : Fin P.K => P.tight f ⊆ P.tightAt x)
    (fun f => (P.tight f).card)
    ⟨P.top, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [PolytopeData.Ok.tight_top P h]
      exact Finset.empty_subset _⟩
  have hf : P.tight f ⊆ P.tightAt x := (Finset.mem_filter.mp hfS).2
  refine ⟨f, ?_⟩
  by_contra hne
  obtain ⟨g, hgsub, hgsub2⟩ := key f hf hne
  have hgS : g ∈ Finset.univ.filter (fun f : Fin P.K => P.tight f ⊆ P.tightAt x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ g, hgsub2⟩
  have hlt : (P.tight f).card < (P.tight g).card := Finset.card_lt_card hgsub
  have hle := hfmax g hgS
  omega

end Work.ConvexCells
