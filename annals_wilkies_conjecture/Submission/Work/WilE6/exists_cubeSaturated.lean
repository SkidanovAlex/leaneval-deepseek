/-
  WilE6 (area E6): cube saturation of a semi-Pfaffian presentation.

  `exists_cubeSaturated` says that, at fixed format bound `F`, any `SemiPf` presentation can be
  replaced, at polynomial cost in the degree, by one whose basic sets have their *holds*-sets
  contained in the cube `[-1,1]^k`.  The construction is the elementary case split of the cube
  along its faces:

  * for a basic set `B` and a subset `S : Finset (Fin k)` of coordinates, add the equations
    `x_i^2 = 1` for `i ∈ S` and the inequalities `1 - x_i^2 > 0` for `i ∉ S`;
  * the union over all `S` of these `satBasic B S` is exactly `(B.holds) ∩ cubeC k`, so the set
    is unchanged, and each individual `satBasic`-set is contained in the cube;
  * each piece costs `3 * k ≤ 3 * F` extra degree and there are `2^k ≤ 2^F` subsets, so the total
    degree grows at most like `2^F (1 + 3F) (D + 1)` — a polynomial in `D` for fixed `F`.

  Duplicates of `B` are removed first (`List.dedup`), which is what makes the number of pieces
  bounded by `D + 1` (a degree-zero basic set is the empty basic set, hence unique).
-/
import Mathlib
import Submission.Work.WilE6.Base

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

attribute [local instance] Classical.decEq

variable {k r : ℕ}

/-! ## §0. List bookkeeping -/

theorem cube_sum_map_const_nat {α : Type*} (l : List α) (c : ℕ) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem cube_sublist_sum_map_le {α : Type*} (f : α → ℕ) {l₁ l₂ : List α}
    (h : List.Sublist l₁ l₂) : (l₁.map f).sum ≤ (l₂.map f).sum := by
  induction h with
  | slnil => simp
  | cons a s ih => simp only [List.map_cons, List.sum_cons]; omega
  | cons_cons a s ih => simp only [List.map_cons, List.sum_cons]; omega

theorem cube_sum_map_deg_add (d : List (Basic k r)) (c : ℕ) :
    (d.map (fun B => B.deg + c)).sum = (d.map Basic.deg).sum + d.length * c := by
  induction d with
  | nil => simp
  | cons B t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem cube_flatMap_sum_deg {α : Type*} (l : List α) (f : α → List (Basic k r)) :
    ((l.flatMap f).map Basic.deg).sum = (l.map (fun a => ((f a).map Basic.deg).sum)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, ih]

/-! ## §1. The two cube atoms -/

/-- The atom `xᵢ² - 1` (the two faces `xᵢ = ±1` of the cube). -/
def cubeEqAtom (k r : ℕ) (i : Fin k) : EAPoly k r :=
  MvPolynomial.X (Sum.inl i) ^ 2 - MvPolynomial.C (1 : ℝ)

/-- The atom `1 - xᵢ²` (strict interior in the `i`-th coordinate). -/
def cubePosAtom (k r : ℕ) (i : Fin k) : EAPoly k r :=
  MvPolynomial.C (1 : ℝ) - MvPolynomial.X (Sum.inl i) ^ 2

@[simp] theorem eaEval_cubeEqAtom (c : EAChain k r) (i : Fin k) (z : Fin k → ℝ) :
    eaEval c (cubeEqAtom k r i) z = z i ^ 2 - 1 := by
  simp [cubeEqAtom, eaEval]

@[simp] theorem eaEval_cubePosAtom (c : EAChain k r) (i : Fin k) (z : Fin k → ℝ) :
    eaEval c (cubePosAtom k r i) z = 1 - z i ^ 2 := by
  simp [cubePosAtom, eaEval]

theorem totalDegree_cubeEqAtom (i : Fin k) : (cubeEqAtom k r i).totalDegree ≤ 2 := by
  have h1 : (MvPolynomial.X (Sum.inl i) ^ 2 : EAPoly k r).totalDegree ≤ 2 := by
    have h := MvPolynomial.totalDegree_pow (MvPolynomial.X (Sum.inl i) : EAPoly k r) 2
    rw [MvPolynomial.totalDegree_X] at h
    simpa using h
  have h2 : (MvPolynomial.C (1 : ℝ) : EAPoly k r).totalDegree ≤ 2 := by
    rw [MvPolynomial.totalDegree_C]; norm_num
  exact le_trans (MvPolynomial.totalDegree_sub (MvPolynomial.X (Sum.inl i) ^ 2)
    (MvPolynomial.C (1 : ℝ))) (max_le h1 h2)

theorem totalDegree_cubePosAtom (i : Fin k) : (cubePosAtom k r i).totalDegree ≤ 2 := by
  have h1 : (MvPolynomial.C (1 : ℝ) : EAPoly k r).totalDegree ≤ 2 := by
    rw [MvPolynomial.totalDegree_C]; norm_num
  have h2 : (MvPolynomial.X (Sum.inl i) ^ 2 : EAPoly k r).totalDegree ≤ 2 := by
    have h := MvPolynomial.totalDegree_pow (MvPolynomial.X (Sum.inl i) : EAPoly k r) 2
    rw [MvPolynomial.totalDegree_X] at h
    simpa using h
  exact le_trans (MvPolynomial.totalDegree_sub (MvPolynomial.C (1 : ℝ))
    (MvPolynomial.X (Sum.inl i) ^ 2)) (max_le h1 h2)

theorem atomDeg_cubeEqAtom (i : Fin k) : atomDeg (cubeEqAtom k r i) ≤ 3 := by
  have h := totalDegree_cubeEqAtom (r := r) i
  simp only [atomDeg]
  omega

theorem atomDeg_cubePosAtom (i : Fin k) : atomDeg (cubePosAtom k r i) ≤ 3 := by
  have h := totalDegree_cubePosAtom (r := r) i
  simp only [atomDeg]
  omega

/-! ## §2. The cube-saturated basic sets -/

/-- Adjoin to `B` the equations `xᵢ² = 1` for `i ∈ S` and the inequalities `1 - xᵢ² > 0`
for `i ∉ S`; the case split over all `S` covers the cube exactly. -/
def satBasic (B : Basic k r) (S : Finset (Fin k)) : Basic k r where
  eqs := B.eqs ++ S.toList.map (cubeEqAtom k r)
  pos := B.pos ++ Sᶜ.toList.map (cubePosAtom k r)

theorem satBasic_holds (B : Basic k r) (S : Finset (Fin k)) (c : EAChain k r) (z : Fin k → ℝ) :
    (satBasic B S).holds c z ↔
      B.holds c z ∧ (∀ i ∈ S, z i ^ 2 = 1) ∧ (∀ i ∉ S, z i ^ 2 < 1) := by
  simp only [satBasic, Basic.holds, List.forall_mem_append, List.forall_mem_map,
    Finset.mem_toList, Finset.mem_compl, eaEval_cubeEqAtom, eaEval_cubePosAtom,
    sub_eq_zero, sub_pos]
  tauto

theorem satBasic_holds_mem_cube (B : Basic k r) (S : Finset (Fin k)) (c : EAChain k r)
    (z : Fin k → ℝ) (h : (satBasic B S).holds c z) : z ∈ cubeC k := by
  rw [satBasic_holds] at h
  change ∀ i, |z i| ≤ 1
  intro i
  by_cases hi : i ∈ S
  · rw [← sq_le_one_iff_abs_le_one, h.2.1 i hi]
  · rw [← sq_le_one_iff_abs_le_one]
    exact le_of_lt (h.2.2 i hi)

theorem basic_deg_of_append (B : Basic k r) (L M : List (EAPoly k r)) :
    (⟨B.eqs ++ L, B.pos ++ M⟩ : Basic k r).deg
      = B.deg + (L.map atomDeg).sum + (M.map atomDeg).sum := by
  simp only [Basic.deg, List.map_append, List.sum_append]
  ring

theorem satBasic_deg_le (B : Basic k r) (S : Finset (Fin k)) :
    (satBasic B S).deg ≤ B.deg + 3 * k := by
  have hA : ((S.toList.map (cubeEqAtom k r)).map atomDeg).sum ≤ 3 * S.card := by
    rw [List.map_map]
    change (S.toList.map (fun i => atomDeg (cubeEqAtom k r i))).sum ≤ 3 * S.card
    calc (S.toList.map (fun i => atomDeg (cubeEqAtom k r i))).sum
        ≤ (S.toList.map (fun _ => 3)).sum :=
          List.sum_le_sum (fun i _ => atomDeg_cubeEqAtom i)
      _ = S.toList.length * 3 := cube_sum_map_const_nat S.toList 3
      _ = S.card * 3 := by rw [Finset.length_toList]
      _ ≤ 3 * S.card := by omega
  have hB : ((Sᶜ.toList.map (cubePosAtom k r)).map atomDeg).sum ≤ 3 * Sᶜ.card := by
    rw [List.map_map]
    change (Sᶜ.toList.map (fun i => atomDeg (cubePosAtom k r i))).sum ≤ 3 * Sᶜ.card
    calc (Sᶜ.toList.map (fun i => atomDeg (cubePosAtom k r i))).sum
        ≤ (Sᶜ.toList.map (fun _ => 3)).sum :=
          List.sum_le_sum (fun i _ => atomDeg_cubePosAtom i)
      _ = Sᶜ.toList.length * 3 := cube_sum_map_const_nat Sᶜ.toList 3
      _ = Sᶜ.card * 3 := by rw [Finset.length_toList]
      _ ≤ 3 * Sᶜ.card := by omega
  have hcard : S.card + Sᶜ.card = k := by
    rw [Finset.card_compl, Fintype.card_fin]
    exact Nat.add_sub_of_le (by simpa using Finset.card_le_univ S)
  rw [show satBasic B S = ⟨B.eqs ++ S.toList.map (cubeEqAtom k r),
      B.pos ++ Sᶜ.toList.map (cubePosAtom k r)⟩ from rfl]
  rw [basic_deg_of_append]
  omega

/-! ## §3. Degree zero basics and the dedup length bound -/

theorem basic_eq_of_eqs_pos {B B' : Basic k r} (h1 : B.eqs = B'.eqs) (h2 : B.pos = B'.pos) :
    B = B' := by
  cases B
  cases B'
  simp_all

theorem basic_deg_eq_zero_iff (B : Basic k r) : B.deg = 0 ↔ B.eqs = [] ∧ B.pos = [] := by
  constructor
  · intro h
    have h' : ∀ x ∈ (B.eqs ++ B.pos).map atomDeg, x = 0 := by
      rw [Basic.deg] at h
      exact List.sum_eq_zero_iff.mp h
    have hempty : B.eqs ++ B.pos = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro Q hQ
      have h2 := h' (atomDeg Q) (List.mem_map.mpr ⟨Q, hQ, rfl⟩)
      simp only [atomDeg] at h2
      omega
    exact List.append_eq_nil_iff.mp hempty
  · rintro ⟨h1, h2⟩
    rw [Basic.deg]
    simp [h1, h2]

theorem cube_nodup_length_le_sum :
    ∀ d : List (Basic k r), d.Nodup → d.length ≤ (d.map Basic.deg).sum + 1 := by
  intro d
  induction d with
  | nil => intro _; simp
  | cons B t ih =>
      intro hd
      rw [List.nodup_cons] at hd
      obtain ⟨hBt, htn⟩ := hd
      have iht := ih htn
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      by_cases hBd : B.deg = 0
      · have hpos : ∀ x ∈ t.map Basic.deg, 1 ≤ x := by
          intro x hx
          obtain ⟨B', hB't, rfl⟩ := List.mem_map.mp hx
          rcases Nat.eq_zero_or_pos B'.deg with h0 | hgt
          · exfalso
            have hB0 : B.eqs = [] ∧ B.pos = [] := (basic_deg_eq_zero_iff B).mp hBd
            have hB'0 : B'.eqs = [] ∧ B'.pos = [] := (basic_deg_eq_zero_iff B').mp h0
            have heq : B' = B := basic_eq_of_eqs_pos (by rw [hB'0.1, hB0.1])
              (by rw [hB'0.2, hB0.2])
            exact hBt (heq ▸ hB't)
          · exact hgt
        have hlen := List.length_le_sum_of_one_le (t.map Basic.deg) hpos
        rw [List.length_map] at hlen
        omega
      · have hge : 1 ≤ B.deg := by omega
        omega

/-! ## §4. The cube-saturated presentation -/

/-- Replace `X` by a presentation whose basic sets are all contained in the cube: for each
basic set and each `S : Finset (Fin k)` add the atoms `xᵢ² = 1` (`i ∈ S`) and `1 - xᵢ² > 0`
(`i ∉ S`).  Duplicates are removed first. -/
def cubeSat (X : SemiPf k) : SemiPf k where
  r := X.r
  c := X.c
  basics := (Finset.univ : Finset (Finset (Fin k))).toList.flatMap
    (fun S => X.basics.dedup.map (fun B => satBasic B S))

@[simp] theorem cubeSat_r (X : SemiPf k) : (cubeSat X).r = X.r := rfl
@[simp] theorem cubeSat_c (X : SemiPf k) : (cubeSat X).c = X.c := rfl
@[simp] theorem cubeSat_fmt (X : SemiPf k) : (cubeSat X).fmt = X.fmt := rfl
@[simp] theorem cubeSat_basics (X : SemiPf k) :
    (cubeSat X).basics = (Finset.univ : Finset (Finset (Fin k))).toList.flatMap
      (fun S => X.basics.dedup.map (fun B => satBasic B S)) := rfl

theorem mem_cubeSat (X : SemiPf k) (z : Fin k → ℝ) :
    z ∈ (cubeSat X).set ↔ z ∈ cubeC k ∧ ∃ B ∈ X.basics, B.holds X.c z := by
  change (z ∈ cubeC k ∧ ∃ B, B ∈ (Finset.univ : Finset (Finset (Fin k))).toList.flatMap
      (fun S => X.basics.dedup.map (fun B => satBasic B S)) ∧ B.holds X.c z) ↔
    (z ∈ cubeC k ∧ ∃ B ∈ X.basics, B.holds X.c z)
  constructor
  · rintro ⟨-, B', hB'mem, hholds⟩
    rw [List.mem_flatMap] at hB'mem
    obtain ⟨S, -, hS⟩ := hB'mem
    rw [List.mem_map] at hS
    obtain ⟨B, hBd, hBeq⟩ := hS
    rw [← hBeq] at hholds
    have hh := (satBasic_holds B S X.c z).mp hholds
    exact ⟨satBasic_holds_mem_cube B S X.c z hholds, B, List.mem_dedup.mp hBd, hh.1⟩
  · rintro ⟨hzcube, B, hBmem, hholds⟩
    refine ⟨hzcube, satBasic B (Finset.univ.filter (fun i => z i ^ 2 = 1)), ?_, ?_⟩
    · rw [List.mem_flatMap]
      refine ⟨Finset.univ.filter (fun i => z i ^ 2 = 1), ?_, ?_⟩
      · exact Finset.mem_toList.mpr (Finset.mem_univ _)
      · rw [List.mem_map]
        exact ⟨B, List.mem_dedup.mpr hBmem, rfl⟩
    · rw [satBasic_holds]
      refine ⟨hholds, ?_, ?_⟩
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i hi
        have hne : z i ^ 2 ≠ 1 := fun hc =>
          hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)
        exact lt_of_le_of_ne ((sq_le_one_iff_abs_le_one (z i)).mpr (hzcube i)) hne

theorem cubeSat_set (X : SemiPf k) : (cubeSat X).set = X.set := by
  ext z
  rw [mem_cubeSat X z]
  exact Iff.rfl

theorem cubeSat_saturates (X : SemiPf k) :
    ∀ B ∈ (cubeSat X).basics, ∀ z : Fin k → ℝ, B.holds (cubeSat X).c z → z ∈ cubeC k := by
  change ∀ B ∈ (Finset.univ : Finset (Finset (Fin k))).toList.flatMap
      (fun S => X.basics.dedup.map (fun B => satBasic B S)),
      ∀ z : Fin k → ℝ, B.holds X.c z → z ∈ cubeC k
  intro B hB z hz
  rw [List.mem_flatMap] at hB
  obtain ⟨S, -, hS⟩ := hB
  rw [List.mem_map] at hS
  obtain ⟨B₀, -, rfl⟩ := hS
  exact satBasic_holds_mem_cube B₀ S X.c z hz

theorem cubeSat_deg_le (X : SemiPf k) :
    (cubeSat X).deg ≤ 2 ^ k * (1 + 3 * k) * (X.deg + 1) := by
  have hnod : X.basics.dedup.Nodup := List.nodup_dedup X.basics
  have hlen : X.basics.dedup.length ≤ (X.basics.dedup.map Basic.deg).sum + 1 :=
    cube_nodup_length_le_sum _ hnod
  have hsub : (X.basics.dedup.map Basic.deg).sum ≤ X.deg := by
    have h := cube_sublist_sum_map_le (Basic.deg (k := k) (r := X.r))
      (List.dedup_sublist X.basics)
    simpa only [WilkiesDesign.E.SemiPf.deg] using h
  have hterm : ∀ S : Finset (Fin k),
      ((X.basics.dedup.map (fun B => satBasic B S)).map Basic.deg).sum
        ≤ (X.basics.dedup.map Basic.deg).sum + 3 * k * X.basics.dedup.length := by
    intro S
    calc ((X.basics.dedup.map (fun B => satBasic B S)).map Basic.deg).sum
        = (X.basics.dedup.map (fun B => (satBasic B S).deg)).sum := by
            rw [List.map_map]; rfl
      _ ≤ (X.basics.dedup.map (fun B => B.deg + 3 * k)).sum :=
            List.sum_le_sum (fun B _ => satBasic_deg_le B S)
      _ = (X.basics.dedup.map Basic.deg).sum + X.basics.dedup.length * (3 * k) :=
            cube_sum_map_deg_add _ _
      _ = (X.basics.dedup.map Basic.deg).sum + 3 * k * X.basics.dedup.length := by ring
  have hlen_list : (Finset.univ : Finset (Finset (Fin k))).toList.length = 2 ^ k := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  have hfin : X.deg + 3 * k * (X.deg + 1) ≤ (1 + 3 * k) * (X.deg + 1) := by
    calc X.deg + 3 * k * (X.deg + 1) ≤ (X.deg + 1) + 3 * k * (X.deg + 1) :=
          Nat.add_le_add_right (Nat.le_succ _) _
      _ = (1 + 3 * k) * (X.deg + 1) := by ring
  calc (cubeSat X).deg
      = (((Finset.univ : Finset (Finset (Fin k))).toList.flatMap
          (fun S => X.basics.dedup.map (fun B => satBasic B S))).map Basic.deg).sum := rfl
    _ = (((Finset.univ : Finset (Finset (Fin k))).toList).map
          (fun S => ((X.basics.dedup.map (fun B => satBasic B S)).map Basic.deg).sum)).sum :=
          cube_flatMap_sum_deg _ _
    _ ≤ (((Finset.univ : Finset (Finset (Fin k))).toList).map
          (fun _ => (X.basics.dedup.map Basic.deg).sum + 3 * k * X.basics.dedup.length)).sum :=
          List.sum_le_sum (fun S _ => hterm S)
    _ = 2 ^ k * ((X.basics.dedup.map Basic.deg).sum + 3 * k * X.basics.dedup.length) := by
          rw [cube_sum_map_const_nat, hlen_list]
    _ ≤ 2 ^ k * (X.deg + 3 * k * (X.deg + 1)) := by
          apply Nat.mul_le_mul_left
          exact add_le_add hsub (Nat.mul_le_mul_left _ (by omega))
    _ ≤ 2 ^ k * ((1 + 3 * k) * (X.deg + 1)) := by
          apply Nat.mul_le_mul_left
          exact hfin
    _ = 2 ^ k * (1 + 3 * k) * (X.deg + 1) := by ring

/-! ## §5. The target -/

theorem exists_cubeSaturated (F : ℕ) : ∃ b : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F → ∃ X' : WilkiesDesign.E.SemiPf k, X'.fmt ≤ F ∧ X'.deg ≤ b.eval X.deg ∧ X'.set = X.set ∧ (∀ B ∈ X'.basics, ∀ z : Fin k → ℝ, B.holds X'.c z → z ∈ WilkiesDesign.E.cubeC k) := by
  refine ⟨Polynomial.C (2 ^ F * (1 + 3 * F)) * (Polynomial.X + 1), ?_⟩
  intro k X hF
  refine ⟨cubeSat X, ?_, ?_, ?_, ?_⟩
  · rw [cubeSat_fmt]; exact hF
  · have hkF : k ≤ F := by
      have h1 : k ≤ X.fmt := by
        rw [WilkiesDesign.E.SemiPf.fmt]; omega
      omega
    have hdeg := cubeSat_deg_le X
    have hb : (Polynomial.C (2 ^ F * (1 + 3 * F)) * (Polynomial.X + 1)).eval X.deg
        = 2 ^ F * (1 + 3 * F) * (X.deg + 1) := by
      simp
    rw [hb]
    calc (cubeSat X).deg ≤ 2 ^ k * (1 + 3 * k) * (X.deg + 1) := hdeg
      _ ≤ 2 ^ F * (1 + 3 * F) * (X.deg + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hkF)
            (by omega)) (le_refl _)
  · exact cubeSat_set X
  · exact cubeSat_saturates X

end Work.WilE6
