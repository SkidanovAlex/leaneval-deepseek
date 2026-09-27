import Mathlib
import Submission.Work.Mostow.KMdefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.Margulis.cosetLemma
import Submission.Work.Mostow.Margulis.cosetLemmaIndex
import Submission.Work.Mostow.Margulis.near1NearId
import Submission.Work.Mostow.margulisCuspDefs
import Submission.Work.Mostow.margulisPair
import Submission.Work.Mostow.abs_mat_le_tpart_actO

/-!
# Margulis index lemma, finite-index form, without `poTransitive`

Same as `Work.Mostow.margulisIndexFinite`, but with `Submission.Work.Mostow.poTransitive`
replaced by `Submission.Work.Mostow.BoostTransitive` (`poTransitive n hn hA = (BoostTransitive n hA).1`),
so that nothing transitively importing `visualDefs` (whose `wvec` collides with `QIDefs.wvec`)
is pulled in.
-/

set_option maxHeartbeats 1000000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

lemma miGid1 (c g : PO n 1) : c * (c⁻¹ * g * c) * c⁻¹ = g := by
  rw [← mul_assoc c (c⁻¹ * g) c, mul_assoc (c * (c⁻¹ * g)) c c⁻¹, mul_inv_cancel, mul_one,
    ← mul_assoc, mul_inv_cancel, one_mul]

lemma miGid2 (c g : PO n 1) : c * (c⁻¹ * g) = g := by
  rw [← mul_assoc, mul_inv_cancel, one_mul]

lemma miGid3 (c g : PO n 1) : (c⁻¹ * g * c) * c⁻¹ = c⁻¹ * g := by
  rw [mul_assoc (c⁻¹ * g) c c⁻¹, mul_inv_cancel, mul_one]

lemma miGid4 (b g : PO n 1) : (b⁻¹ * g * b)⁻¹ = b⁻¹ * g⁻¹ * b := by
  rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc b⁻¹ g⁻¹ b]

lemma miGid5 (b g h : PO n 1) : (b⁻¹ * g * b)⁻¹ * (b⁻¹ * h * b) = b⁻¹ * (g⁻¹ * h) * b := by
  rw [miGid4, mul_assoc (b⁻¹ * g⁻¹) b (b⁻¹ * h * b), ← mul_assoc b (b⁻¹ * h) b,
    ← mul_assoc b b⁻¹ h, mul_inv_cancel, one_mul, ← mul_assoc (b⁻¹ * g⁻¹) h b,
    ← mul_assoc b⁻¹ g⁻¹ h]

lemma miGid6 (c g : PO n 1) : g * c = c * (c⁻¹ * g * c) := by
  rw [← mul_assoc c (c⁻¹ * g) c, miGid2]

def miCB : ℝ := Real.cosh 1 + 2

lemma miOneLeCB : (1:ℝ) ≤ miCB := by
  have h : (1:ℝ) ≤ Real.cosh 1 := Real.one_le_cosh 1
  simp only [miCB]; linarith

lemma miCBPos : 0 < miCB := lt_of_lt_of_le one_pos miOneLeCB

lemma miCBNe : miCB ≠ 0 := ne_of_gt miCBPos

lemma miNear1Mono {A : O1 n} {q q' : ℝ} (h : Near1 A q) (hle : q ≤ q') : Near1 A q' :=
  fun i j => le_trans (h i j) hle

lemma miAbsMatToOLe {g : PO n 1} (hg : hdist (0 : E n) (g • (0 : E n)) ≤ 1)
    (i j : Fin n ⊕ Fin 1) : |mat (ToO g) i j| ≤ miCB := by
  have h1 : Near1 (ToO g) (Real.cosh 1 + 1) := Near1_ToO_of_hdist (by norm_num) hg
  have h2 := abs_entry_le h1 i j
  have h3 : |dE n i j| ≤ 1 := abs_dE_le i j
  simp only [miCB] at *
  linarith

def miLabK (K : ℕ) (x : ℝ) : Fin (K+1) :=
  ⟨min (Nat.floor ((x + miCB) * (K:ℝ) / (2*miCB))) K, by
    have h := Nat.min_le_right (Nat.floor ((x + miCB) * (K:ℝ) / (2*miCB))) K
    omega⟩

lemma miLabKVal (K : ℕ) {x : ℝ} (hx : -miCB ≤ x) (hx1 : x ≤ miCB) :
    (miLabK K x : ℕ) = Nat.floor ((x + miCB) * (K:ℝ) / (2*miCB)) := by
  have h2CB : (0:ℝ) < 2*miCB := by have := miCBPos; linarith
  have hle : (x + miCB) * (K:ℝ) / (2*miCB) ≤ K := by
    rw [div_le_iff₀ h2CB]
    have h2 : x + miCB ≤ 2*miCB := by linarith
    calc (x + miCB) * (K:ℝ) ≤ (2*miCB) * K :=
          mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg K)
      _ = K * (2*miCB) := by ring
  have hfl : Nat.floor ((x + miCB) * (K:ℝ) / (2*miCB)) ≤ K := Nat.floor_le_of_le hle
  simp only [miLabK]
  exact Nat.min_eq_left hfl

lemma miLabKClose (K : ℕ) (hK : 0 < K) {x y : ℝ} (hx0 : -miCB ≤ x) (hx1 : x ≤ miCB)
    (hy0 : -miCB ≤ y) (hy1 : y ≤ miCB) (h : miLabK K x = miLabK K y) : |x - y| ≤ 4*miCB/K := by
  set t : ℝ := (x + miCB) * (K:ℝ) / (2*miCB) with ht
  set s : ℝ := (y + miCB) * (K:ℝ) / (2*miCB) with hs
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hKne : (K:ℝ) ≠ 0 := ne_of_gt hKpos
  have h2CB : (0:ℝ) < 2*miCB := by have := miCBPos; linarith
  have h2CBne : (2*miCB:ℝ) ≠ 0 := ne_of_gt h2CB
  have ht0 : 0 ≤ t := by
    rw [ht]; exact div_nonneg (mul_nonneg (by linarith) (le_of_lt hKpos)) (le_of_lt h2CB)
  have hs0 : 0 ≤ s := by
    rw [hs]; exact div_nonneg (mul_nonneg (by linarith) (le_of_lt hKpos)) (le_of_lt h2CB)
  have hfl : Nat.floor t = Nat.floor s := by
    have hv : (miLabK K x : ℕ) = (miLabK K y : ℕ) := congrArg Fin.val h
    rw [miLabKVal K hx0 hx1, miLabKVal K hy0 hy1] at hv
    rw [ht, hs]
    exact hv
  have hts : |t - s| ≤ 2 := by
    have h1 : |t - (Nat.floor t : ℝ)| ≤ 1 := Nat.abs_sub_floor_le ht0
    have h2 : |s - (Nat.floor s : ℝ)| ≤ 1 := Nat.abs_sub_floor_le hs0
    have h3 : |(Nat.floor t : ℝ) - s| = |s - (Nat.floor s : ℝ)| := by
      rw [abs_sub_comm, hfl]
    calc |t - s| = |(t - (Nat.floor t : ℝ)) + ((Nat.floor t : ℝ) - s)| := by ring_nf
      _ ≤ |t - (Nat.floor t : ℝ)| + |(Nat.floor t : ℝ) - s| := abs_add_le _ _
      _ ≤ 2 := by rw [h3]; linarith
  have hts_eq : t - s = (x - y) * ((K:ℝ) / (2*miCB)) := by
    rw [ht, hs]; ring
  have hmul : ((K:ℝ) / (2*miCB)) * (2*miCB/K) = 1 := by
    field_simp
    rw [div_self miCBNe]
  have hxy : x - y = (t - s) * (2*miCB/K) := by
    calc x - y = (x - y) * 1 := by ring
      _ = (x - y) * (((K:ℝ) / (2*miCB)) * (2*miCB/K)) := by rw [hmul]
      _ = ((x - y) * ((K:ℝ) / (2*miCB))) * (2*miCB/K) := by ring
      _ = (t - s) * (2*miCB/K) := by rw [← hts_eq]
  have h4 : (0:ℝ) ≤ 2*miCB/K := div_nonneg (by linarith [miCBPos]) (le_of_lt hKpos)
  calc |x - y| = |(t - s) * (2*miCB/K)| := by rw [hxy]
    _ = |t - s| * (2*miCB/K) := by rw [abs_mul, abs_of_nonneg h4]
    _ ≤ 2 * (2*miCB/K) := mul_le_mul_of_nonneg_right hts h4
    _ = 4*miCB/K := by ring

def miCellZero (K : ℕ) :
    PO n 1 → Fin (Fintype.card ((Fin n ⊕ Fin 1) → (Fin n ⊕ Fin 1) → Fin (K+1))) :=
  fun g => Fintype.equivFin _ (fun i j => miLabK K (mat (ToO g) i j))

lemma miCellZeroClose (K : ℕ) (hK : 0 < K) {g h : PO n 1}
    (hg : hdist (0 : E n) (g • (0 : E n)) ≤ 1)
    (hh : hdist (0 : E n) (h • (0 : E n)) ≤ 1)
    (heq : miCellZero (n:=n) K g = miCellZero (n:=n) K h) :
    ∀ i j, |mat (ToO g) i j - mat (ToO h) i j| ≤ 4*miCB/K := by
  intro i j
  have htuple : (fun i j => miLabK K (mat (ToO g) i j))
      = (fun i j => miLabK K (mat (ToO h) i j)) :=
    (Fintype.equivFin ((Fin n ⊕ Fin 1) → (Fin n ⊕ Fin 1) → Fin (K+1))).injective heq
  have hlab : miLabK K (mat (ToO g) i j) = miLabK K (mat (ToO h) i j) :=
    congrFun (congrFun htuple i) j
  have hgB : |mat (ToO g) i j| ≤ miCB := miAbsMatToOLe hg i j
  have hhB : |mat (ToO h) i j| ≤ miCB := miAbsMatToOLe hh i j
  exact miLabKClose K hK (abs_le.mp hgB).1 (abs_le.mp hgB).2 (abs_le.mp hhB).1 (abs_le.mp hhB).2 hlab

lemma miNear1ToOInv (n : ℕ) (hA : POActionProp n) {g : PO n 1}
    (hg : hdist (0 : E n) (g • (0 : E n)) ≤ 1) (i j : Fin n ⊕ Fin 1) :
    |mat (ToO (g⁻¹)) i j| ≤ miCB := by
  have h1 : Near1 (ToO g) (Real.cosh 1 + 1) := Near1_ToO_of_hdist (by norm_num) hg
  have h2 : |mat ((ToO g)⁻¹) i j| ≤ 1 + (Real.cosh 1 + 1) :=
    abs_inv_entry_le' h1 (by positivity) i j
  have h3 : mat ((ToO g)⁻¹) i j = mat (ToO (g⁻¹)) i j := by rw [← ToO_inv hA]
  rw [h3] at h2
  simp only [miCB] at *
  linarith

lemma miCellZeroNear (n : ℕ) (hA : POActionProp n) (K : ℕ) (hK : 0 < K) {g h : PO n 1}
    (hg : hdist (0 : E n) (g • (0 : E n)) ≤ 1)
    (hh : hdist (0 : E n) (h • (0 : E n)) ≤ 1)
    (heq : miCellZero (n:=n) K g = miCellZero (n:=n) K h) :
    Near1 (ToO (g⁻¹ * h)) (msz n * miCB * (4*miCB/K)) := by
  intro i j
  have hD := miCellZeroClose (n:=n) K hK hg hh heq
  have hmat : mat (ToO (g⁻¹ * h)) = mat (ToO (g⁻¹)) * mat (ToO h) := by
    rw [ToO_mul hA, mat_mul_coe]
  have hone : mat (ToO (g⁻¹)) * mat (ToO g) = 1 := by
    rw [← mat_mul_coe, ← ToO_mul hA, inv_mul_cancel, ToO_one hA, mat_one_coe]
  have honee : (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) i j = dE n i j := by
    rw [← mat_one_coe, mat_one_entry]
  have hEq : mat (ToO (g⁻¹)) * (mat (ToO h) - mat (ToO g))
      = mat (ToO (g⁻¹)) * mat (ToO h) - 1 := by
    rw [Matrix.mul_sub, hone]
  have hid2 : (mat (ToO (g⁻¹)) * mat (ToO h)) i j - dE n i j
      = (mat (ToO (g⁻¹)) * (mat (ToO h) - mat (ToO g))) i j := by
    rw [← honee, ← Matrix.sub_apply, ← hEq]
  have hid : mat (ToO (g⁻¹ * h)) i j - dE n i j
      = (mat (ToO (g⁻¹)) * (mat (ToO h) - mat (ToO g))) i j := by
    rw [hmat]; exact hid2
  rw [hid]
  have hstep : |(mat (ToO (g⁻¹)) * (mat (ToO h) - mat (ToO g))) i j|
      ≤ ∑ k : Fin n ⊕ Fin 1, |mat (ToO (g⁻¹)) i k| * |(mat (ToO h) - mat (ToO g)) k j| := by
    rw [Matrix.mul_apply]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum (fun k _ => by rw [abs_mul])
  refine le_trans hstep ?_
  have h2 : ∀ k : Fin n ⊕ Fin 1, |mat (ToO (g⁻¹)) i k| * |(mat (ToO h) - mat (ToO g)) k j|
      ≤ miCB * (4*miCB/K) := by
    intro k
    have h4 : |(mat (ToO h) - mat (ToO g)) k j| ≤ 4*miCB/K := by
      rw [Matrix.sub_apply, abs_sub_comm]
      exact hD k j
    exact mul_le_mul (miNear1ToOInv n hA hg i k) h4 (abs_nonneg _) (by linarith [miCBPos])
  refine le_trans (Finset.sum_le_sum (fun k _ => h2 k)) ?_
  rw [sum_const_sum]
  exact le_of_eq (by ring)

/-- the cell cover at `x = 0` -/
theorem miCellCoverZero (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∀ η : ℝ, 0 < η → ∃ m : ℕ, ∃ cell : PO n 1 → Fin m,
      ∀ g h : PO n 1, hdist (0 : E n) (g • (0 : E n)) ≤ 1 →
        hdist (0 : E n) (h • (0 : E n)) ≤ 1 → cell g = cell h → NearIdAt (g⁻¹ * h) (0 : E n) η := by
  intro η hη
  obtain ⟨q, hqpos, hq⟩ := Work.Mostow.Margulis.near1NearId n hn hA hI η hη
  set c : ℝ := msz n * miCB * (4*miCB) with hc
  have hcpos : 0 < c := by
    rw [hc]
    have h1 : (0:ℝ) < msz n := lt_of_lt_of_le zero_lt_one (one_le_msz n)
    have h2 : 0 < miCB := miCBPos
    positivity
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (c / q)
  set K : ℕ := max K₀ 1 with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num : 0 < 1) (Nat.le_max_right _ _)
  have hKpos' : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
  have hKgt : c / q < (K:ℝ) := lt_of_lt_of_le hK₀ (by exact_mod_cast Nat.le_max_left K₀ 1)
  have hcK : msz n * miCB * (4*miCB/K) = c / K := by
    rw [hc, ← mul_div_assoc]
  have hle : c / (K:ℝ) ≤ q := by
    rw [div_le_iff₀ hKpos']
    have h := hKgt
    rw [div_lt_iff₀ hqpos] at h
    linarith
  refine ⟨_, miCellZero (n:=n) K, fun g h hg hh heq => ?_⟩
  refine hq (g⁻¹ * h) (miNear1Mono (miCellZeroNear n hA K hKpos hg hh heq) ?_)
  rw [hcK]; exact hle

lemma miNearIdAtConj {c g : PO n 1} {η : ℝ} (hA : POActionProp n) (hI : HypIsometryProp n)
    (h : NearIdAt (c⁻¹ * g * c) (0 : E n) η) : NearIdAt g (c • (0 : E n)) η := by
  have hsmul : ∀ (a b : PO n 1) (u : E n), (a * b) • u = a • (b • u) := hA.2.2.2.2.1
  have hiso : ∀ (a : PO n 1) (u v : E n), hdist (a • u) (a • v) = hdist u v := hI.2.2.2.2.2.2.1
  intro u hu
  have hv : hdist (0 : E n) (c⁻¹ • u) ≤ 1 := by
    have h1 := hiso c (0 : E n) (c⁻¹ • u)
    have h2 : c • (c⁻¹ • u) = u := by rw [← hsmul, mul_inv_cancel, hA.2.2.2.1]
    rw [h2] at h1
    rw [← h1]; exact hu
  have h3 := h (c⁻¹ • u) hv
  have key : hdist u (g • u) = hdist (c⁻¹ • u) ((c⁻¹ * g * c) • (c⁻¹ • u)) := by
    have h6 : c • ((c⁻¹ * g * c) • (c⁻¹ • u)) = g • u := by
      rw [← hsmul, ← hsmul, miGid1]
    have h7 := hiso c (c⁻¹ • u) ((c⁻¹ * g * c) • (c⁻¹ • u))
    have h8 : c • (c⁻¹ • u) = u := by rw [← hsmul, mul_inv_cancel, hA.2.2.2.1]
    rw [h6, h8] at h7
    exact h7
  rw [key]; exact h3

/-- the general cell cover -/
lemma miHdistShift (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) (b k : PO n 1) :
    hdist (0 : E n) ((b⁻¹ * k * b) • (0 : E n))
      = hdist (b • (0 : E n)) (k • (b • (0 : E n))) := by
  have hsmul : ∀ (a c : PO n 1) (u : E n), (a * c) • u = a • (c • u) := hA.2.2.2.2.1
  have hiso : ∀ (a : PO n 1) (u v : E n), hdist (a • u) (a • v) = hdist u v := hI.2.2.2.2.2.2.1
  have h1 : (b⁻¹ * k * b) • (0 : E n) = b⁻¹ • (k • (b • (0 : E n))) := by
    rw [hsmul, hsmul]
  rw [h1]
  have h2 := hiso b (0 : E n) (b⁻¹ • (k • (b • (0 : E n))))
  have h3 : b • (b⁻¹ • (k • (b • (0 : E n)))) = k • (b • (0 : E n)) := by
    rw [← hsmul, mul_inv_cancel, hA.2.2.2.1]
  rw [h3] at h2
  exact h2.symm

theorem miCellCoverAux (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∀ η : ℝ, 0 < η → ∃ m : ℕ, ∀ x : E n, ∃ cell : PO n 1 → Fin m,
      ∀ g h : PO n 1, hdist x (g • x) ≤ 1 → hdist x (h • x) ≤ 1 →
        cell g = cell h → NearIdAt (g⁻¹ * h) x η := by
  intro η hη
  obtain ⟨m, cell0, hcell0⟩ := miCellCoverZero n hn hA hI η hη
  refine ⟨m, fun x => ?_⟩
  obtain ⟨b, hb⟩ := (BoostTransitive n hA).1 x
  refine ⟨fun g => cell0 (b⁻¹ * g * b), ?_⟩
  intro g h hg hh heq
  have hg' : hdist (0 : E n) ((b⁻¹ * g * b) • (0 : E n)) ≤ 1 := by
    rw [miHdistShift n hA hI b g, hb]; exact hg
  have hh' : hdist (0 : E n) ((b⁻¹ * h * b) • (0 : E n)) ≤ 1 := by
    rw [miHdistShift n hA hI b h, hb]; exact hh
  have hcell' := hcell0 (b⁻¹ * g * b) (b⁻¹ * h * b) hg' hh' heq
  have hEq : (b⁻¹ * g * b)⁻¹ * (b⁻¹ * h * b) = b⁻¹ * (g⁻¹ * h) * b := miGid5 b g h
  have hcell'' : NearIdAt (b⁻¹ * (g⁻¹ * h) * b) (0 : E n) η := hEq ▸ hcell'
  have hfin := miNearIdAtConj (c := b) (g := g⁻¹ * h) hA hI hcell''
  rwa [hb] at hfin

lemma miListDisp (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) {Δ : Subgroup (PO n 1)}
    {x : E n} {ε : ℝ} (l : List Δ)
    (h : ∀ g ∈ l, hdist x (((g : Δ) : PO n 1) • x) < ε) :
    hdist x (((l.prod : Δ) : PO n 1) • x) ≤ (l.length : ℝ) * ε := by
  have hsmul : ∀ (a b : PO n 1) (u : E n), (a * b) • u = a • (b • u) := hA.2.2.2.2.1
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hiso : ∀ (a : PO n 1) (u v : E n), hdist (a • u) (a • v) = hdist u v := hI.2.2.2.2.2.2.1
  have htri : ∀ u v w : E n, hdist u w ≤ hdist u v + hdist v w := hI.2.2.2.1
  have hzero : hdist x x = 0 := (hI.2.2.1 x x).mpr rfl
  induction l with
  | nil =>
      have h1 : hdist x (((([] : List Δ).prod : Δ) : PO n 1) • x) = 0 := by
        rw [show (((([] : List Δ).prod : Δ) : PO n 1)) = 1 from rfl, hone, hzero]
      rw [h1]
      simp
  | cons g t ih =>
      have hg : hdist x (((g : Δ) : PO n 1) • x) ≤ ε := le_of_lt (h g (by simp))
      have ht : ∀ c ∈ t, hdist x (((c : Δ) : PO n 1) • x) < ε := fun c hc => h c (by simp [hc])
      have ih' := ih ht
      have hcoe : (((g :: t).prod : Δ) : PO n 1) = (g : PO n 1) * ((t.prod : Δ) : PO n 1) := rfl
      rw [hcoe]
      have hstep : hdist x (((g : PO n 1) * ((t.prod : Δ) : PO n 1)) • x)
          ≤ hdist x ((g : PO n 1) • x)
            + hdist ((g : PO n 1) • x) ((g : PO n 1) • (((t.prod : Δ) : PO n 1) • x)) := by
        rw [hsmul]; exact htri _ _ _
      refine le_trans hstep ?_
      rw [hiso]
      have hlen : (((g :: t).length : ℕ) : ℝ) = (t.length : ℝ) + 1 := by
        rw [List.length_cons]; push_cast; ring
      rw [hlen]
      linarith


theorem margulisIndexFiniteQ (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∃ m : ℕ,
      ∀ Γ : Subgroup (PO n 1), IsDiscrete (SetLike.coe Γ) → ∀ x : E n,
        let Δ : Subgroup (PO n 1) := Subgroup.closure {g | g ∈ Γ ∧ hdist x (g • x) < ε}
        let N : Subgroup (PO n 1) := Subgroup.closure {g | g ∈ Δ ∧ NearIdAt g x η}
        (N.subgroupOf Δ).FiniteIndex ∧ (N.subgroupOf Δ).index ≤ m := by
  intro η hη
  obtain ⟨m, hm⟩ := miCellCoverAux n hn hA hI η hη
  refine ⟨1/(m+1), by positivity, m, fun Γ _ x => ?_⟩
  obtain ⟨cell, hcell⟩ := hm x
  have hsmul : ∀ (a b : PO n 1) (u : E n), (a * b) • u = a • (b • u) := hA.2.2.2.2.1
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hiso : ∀ (a : PO n 1) (u v : E n), hdist (a • u) (a • v) = hdist u v := hI.2.2.2.2.2.2.1
  have heps : (0:ℝ) < 1/(m+1) := by positivity
  let S0 : Set (PO n 1) := {g | g ∈ Γ ∧ hdist x (g • x) < 1/(m+1)}
  let Δ : Subgroup (PO n 1) := Subgroup.closure S0
  let N : Subgroup (PO n 1) := Subgroup.closure {g | g ∈ Δ ∧ NearIdAt g x η}
  let S : Set Δ := {g : Δ | hdist x (((g : Δ) : PO n 1) • x) < 1/(m+1)}
  have main : m < (N.subgroupOf Δ).index ∨ (N.subgroupOf Δ).index = 0 → False := by
    intro hcard
    have hgen : Subgroup.closure S = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro g
      have hmem : (g : PO n 1) ∈ Subgroup.closure S0 := g.2
      have key := Subgroup.closure_induction
        (p := fun y hy => (⟨y, hy⟩ : Δ) ∈ Subgroup.closure S) ?_ ?_ ?_ ?_ hmem
      · rwa [show (⟨(g : PO n 1), hmem⟩ : Δ) = g from Subtype.ext rfl] at key
      · intro y hy
        refine Subgroup.subset_closure ?_
        exact hy.2
      · exact Subgroup.one_mem _
      · intro y z hy hz ihy ihz
        change (⟨y, hy⟩ : Δ) * ⟨z, hz⟩ ∈ Subgroup.closure S
        exact Subgroup.mul_mem _ ihy ihz
      · intro y hy ihy
        change (⟨y, hy⟩ : Δ)⁻¹ ∈ Subgroup.closure S
        exact Subgroup.inv_mem _ ihy
    have hsymmD : ∀ g : Δ, hdist x (((g⁻¹ : Δ) : PO n 1) • x)
        = hdist x (((g : Δ) : PO n 1) • x) := by
      intro g
      have hcoe : ((g⁻¹ : Δ) : PO n 1) = (g : PO n 1)⁻¹ := rfl
      rw [hcoe]
      have h1 : hdist ((g : PO n 1) • x) ((g : PO n 1) • ((g : PO n 1)⁻¹ • x))
          = hdist x ((g : PO n 1)⁻¹ • x) := hiso _ _ _
      have h2 : (g : PO n 1) • ((g : PO n 1)⁻¹ • x) = x := by rw [← hsmul, mul_inv_cancel, hone]
      rw [h2] at h1
      rw [← h1, hI.2.1]
    have hSsymm : S = S⁻¹ := by
      ext g
      rw [Set.mem_inv]
      constructor
      · intro hg
        show hdist x (((g⁻¹ : Δ) : PO n 1) • x) < 1/(m+1)
        rw [hsymmD g]
        exact hg
      · intro hg
        show hdist x (((g : Δ) : PO n 1) • x) < 1/(m+1)
        rw [← hsymmD g]
        exact hg
    obtain ⟨a, hshort, hcoset⟩ :=
      Work.Mostow.Margulis.cosetLemmaIndex S (N.subgroupOf Δ) m hgen hSsymm hcard
    have hDle : ∀ i, hdist x (((a i : Δ) : PO n 1) • x) ≤ 1 := by
      intro i
      obtain ⟨l, hlen, hmeml, hprod⟩ := hshort i
      have h1 := miListDisp n hA hI l hmeml
      have h2 : hdist x (((a i : Δ) : PO n 1) • x) ≤ (l.length : ℝ) * (1/(m+1)) := by
        rw [← hprod]; exact h1
      have h3 : (l.length : ℝ) * (1/(m+1)) ≤ (m:ℝ) * (1/(m+1)) := by
        have hh : (l.length : ℝ) ≤ (m:ℝ) := by exact_mod_cast hlen
        exact mul_le_mul_of_nonneg_right hh (le_of_lt heps)
      have h4 : (m:ℝ) * (1/(m+1)) < 1 := by
        rw [mul_one_div, div_lt_one (by positivity)]
        exact_mod_cast Nat.lt_succ_self m
      linarith
    set f : Fin (m+1) → Fin m := fun i => cell ((a i : Δ) : PO n 1) with hf
    have hcard2 : Fintype.card (Fin m) < Fintype.card (Fin (m+1)) := by simp
    obtain ⟨i, j, hij, heqij⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard2
    have hnear : NearIdAt (((a i)⁻¹ * (a j) : Δ) : PO n 1) x η := by
      have h1 := hcell ((a i : Δ) : PO n 1) ((a j : Δ) : PO n 1) (hDle i) (hDle j) heqij
      simpa using h1
    have hmemN : (a i)⁻¹ * (a j) ∈ N.subgroupOf Δ := by
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.subset_closure ⟨((a i)⁻¹ * (a j)).2, ?_⟩
      exact hnear
    exact absurd hmemN (hcoset i j hij)
  refine ⟨?_, ?_⟩
  · rw [Subgroup.finiteIndex_iff]
    intro h0
    exact main (Or.inr h0)
  · by_contra hcon
    exact main (Or.inl (lt_of_not_ge hcon))


end

end Work.Mostow
