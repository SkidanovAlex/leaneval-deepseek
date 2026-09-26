import Mathlib
import Submission.Work.SG.SGRepDefs

/-!
# `RepCoh_cobsig`: the coboundary `σ` attached to an `H¹` representative

Given a vector `y` whose difference with the `h`-th `H¹` representative of the arithmetic
class `j` lies in the `ℤ`-span of the coboundary lattice `Bl` (with coefficients `lam`), we
exhibit `σ : ℤ³` such that
* `n ∣ (1 - g) σ` for every generator `g` of the point group (`n = (Ad j).n`), and
* the integral coboundary model `cz j σ` reproduces the difference
  `y - reps[h]` modulo `n` coordinate by coordinate.

`σ` is the `lam`-linear combination of the `σ`-vectors stored alongside the echelon basis
rows of `Bl`.  The two assertions are the coordinate form of the certified facts
`row_c ≡ cobVec n σ_c (mod n)` (`Cd_Bl_cob`) and `n ∣ (1 - g) σ_c` (`Cd_Bl_sig`), transported
through the linearity of `Data.lin`.
-/

namespace Work.SG

/-! ## Elementary `V3` algebra (coordinate lemmas for the flat vector type) -/

private theorem cobsig_toFun_add (u v : Data.V3) :
    (Data.V3.add u v).toFun = u.toFun + v.toFun := by
  funext c; fin_cases c <;> rfl

private theorem cobsig_toFun_sub (u v : Data.V3) :
    (Data.V3.sub u v).toFun = u.toFun - v.toFun := by
  funext c; fin_cases c <;> rfl

private theorem cobsig_toFun_smul (k : ℤ) (u : Data.V3) :
    (Data.V3.smul k u).toFun = k • u.toFun := by
  funext c; fin_cases c <;> rfl

private theorem cobsig_toFun_zero : Data.V3.zero.toFun = 0 := by
  funext c; fin_cases c <;> rfl

private theorem cobsig_toFun_ediv (u : Data.V3) (n : ℤ) :
    (Data.V3.ediv u n).toFun = fun c => u.toFun c / n := by
  funext c; fin_cases c <;> rfl

private theorem cobsig_mulV_zero (A : Data.M3) :
    Data.M3.mulV A Data.V3.zero = Data.V3.zero := by
  apply CZ.toFun_inj
  simp only [CZ.toIMat_mulV, cobsig_toFun_zero, Matrix.mulVec_zero]

private theorem cobsig_sub_self (u : Data.V3) : Data.V3.sub u u = Data.V3.zero := by
  apply CZ.toFun_inj
  simp only [cobsig_toFun_sub, cobsig_toFun_zero]
  funext c; simp [Pi.sub_apply]

private theorem cobsig_dvd_zero (n : ℤ) : Data.V3.dvd n Data.V3.zero = true := by
  simp [Data.V3.dvd, Data.V3.zero]

private theorem cobsig_dvd_add {n : ℤ} {u v : Data.V3} (hu : Data.V3.dvd n u = true)
    (hv : Data.V3.dvd n v = true) : Data.V3.dvd n (Data.V3.add u v) = true :=
  (RC.dvd_iff_toFun n _).mpr (fun c => by
    rw [cobsig_toFun_add]
    exact Int.dvd_add ((RC.dvd_iff_toFun n u).mp hu c) ((RC.dvd_iff_toFun n v).mp hv c))

private theorem cobsig_dvd_smul {n : ℤ} {u : Data.V3} (k : ℤ)
    (hu : Data.V3.dvd n u = true) : Data.V3.dvd n (Data.V3.smul k u) = true :=
  (RC.dvd_iff_toFun n _).mpr (fun c => by
    rw [cobsig_toFun_smul]
    exact dvd_mul_of_dvd_right ((RC.dvd_iff_toFun n u).mp hu c) k)

private theorem cobsig_ediv_zero (n : ℤ) : Data.V3.ediv Data.V3.zero n = Data.V3.zero := by
  apply CZ.toFun_inj
  simp only [cobsig_toFun_ediv, cobsig_toFun_zero]
  funext c; simp

private theorem cobsig_ediv_add {n : ℤ} {u v : Data.V3} (hu : Data.V3.dvd n u = true) :
    Data.V3.ediv (Data.V3.add u v) n
      = Data.V3.add (Data.V3.ediv u n) (Data.V3.ediv v n) := by
  apply CZ.toFun_inj
  simp only [cobsig_toFun_ediv, cobsig_toFun_add]
  funext c
  exact Int.add_ediv_of_dvd_left ((RC.dvd_iff_toFun n u).mp hu c)

private theorem cobsig_ediv_smul {n : ℤ} {u : Data.V3} (k : ℤ)
    (hu : Data.V3.dvd n u = true) :
    Data.V3.ediv (Data.V3.smul k u) n = Data.V3.smul k (Data.V3.ediv u n) := by
  apply CZ.toFun_inj
  simp only [cobsig_toFun_ediv, cobsig_toFun_smul]
  funext c
  exact Int.mul_ediv_assoc k ((RC.dvd_iff_toFun n u).mp hu c)

/-- The one-step linearity identity `(1 - A)(c u + r) = c (1 - A)u + (1 - A)r`. -/
private theorem cobsig_lin_decomp (A : Data.M3) (k : ℤ) (u r : Data.V3) :
    Data.V3.sub (Data.V3.add (Data.V3.smul k u) r)
        (Data.M3.mulV A (Data.V3.add (Data.V3.smul k u) r))
      = Data.V3.add (Data.V3.smul k (Data.V3.sub u (Data.M3.mulV A u)))
          (Data.V3.sub r (Data.M3.mulV A r)) := by
  apply CZ.toFun_inj
  simp only [cobsig_toFun_sub, cobsig_toFun_add, cobsig_toFun_smul, CZ.toIMat_mulV,
    Matrix.mulVec_add, Matrix.mulVec_smul]
  funext c
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-! ## Extraction of coordinates from blocks -/

private theorem cobsig_unblocks_length (vs : List Data.V3) :
    (Data.unblocks vs).length = 3 * vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      have hunb : Data.unblocks (v :: vs) = v.toList ++ Data.unblocks vs := by
        rw [Data.unblocks, List.flatMap_cons]; rfl
      rw [hunb, List.length_append, ih]
      simp [Data.V3.toList]
      ring

private theorem cobsig_exists_three (l : List ℤ) (h : 3 ≤ l.length) :
    ∃ x y z r, l = x :: y :: z :: r := by
  match l with
  | x :: y :: z :: r => exact ⟨x, y, z, r, rfl⟩
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h

/-- The `c`-th coordinate of the `g`-th block of a flat vector. -/
private theorem cobsig_blk_toFun (v : List ℤ) (g : ℕ) (c : Fin 3)
    (h : 3 * (g + 1) ≤ v.length) : (RC.blk v g).toFun c = v.getD (3 * g + c.val) 0 := by
  induction g generalizing v with
  | zero =>
      obtain ⟨x, y, z, r, rfl⟩ := cobsig_exists_three v (by omega)
      fin_cases c <;> simp [RC.blk, Data.blocks, Data.V3.toFun]
  | succ g ih =>
      obtain ⟨x, y, z, r, rfl⟩ := cobsig_exists_three v (by omega)
      have hlen : 3 * (g + 1) ≤ r.length := by simp only [List.length_cons] at h; omega
      have hidx : 3 * (g + 1) + c.val = (3 * g + c.val) + 3 := by omega
      rw [hidx, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
      show (RC.blk r g).toFun c = r.getD (3 * g + c.val) 0
      exact ih r hlen

/-- Coordinate extraction from `Data.unblocks`. -/
private theorem cobsig_unblocks_getD (vs : List Data.V3) (g : ℕ) (c : Fin 3)
    (hg : g < vs.length) :
    (Data.unblocks vs).getD (3 * g + c.val) 0 = (vs.getD g Data.V3.zero).toFun c := by
  have hlen : 3 * (g + 1) ≤ (Data.unblocks vs).length := by
    rw [cobsig_unblocks_length]; omega
  rw [← cobsig_blk_toFun (Data.unblocks vs) g c hlen]
  simp only [RC.blk, RC.blocks_unblocks]

/-- Coordinate extraction for `List.map`. -/
private theorem cobsig_getD_map {α β : Type*} (l : List α) (f : α → β) (d : α) (d' : β)
    (i : ℕ) (hi : i < l.length) : (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map,
    List.getD_eq_getElem _ _ hi]

/-! ## Linearity of `Data.lin` -/

private theorem cobsig_lin_toFun (l : List Data.V3) (cs : List ℤ) (c : Fin 3) :
    (Data.lin l cs).toFun c =
      ((List.range l.length).map (fun i => cs.getD i 0 * (l.getD i Data.V3.zero).toFun c)).sum := by
  induction l generalizing cs with
  | nil => cases cs <;> (fin_cases c <;> simp [Data.lin, cobsig_toFun_zero])
  | cons v vs ih =>
      cases cs with
      | nil => fin_cases c <;> simp [Data.lin, cobsig_toFun_zero]
      | cons c0 cs' =>
          rw [Data.lin, List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons,
            List.map_map]
          have hcomp : ((fun i => (c0 :: cs').getD i 0 *
                ((v :: vs).getD i Data.V3.zero).toFun c) ∘ Nat.succ)
              = (fun j => cs'.getD j 0 * (vs.getD j Data.V3.zero).toFun c) := by
            funext j; simp only [Function.comp_apply, List.getD_cons_succ]
          rw [hcomp, ← ih]
          simp only [List.getD_cons_zero, cobsig_toFun_add, cobsig_toFun_smul, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul]

/-- `n` divides `(1 - A) σ` for `σ` the `lam`-combination of vectors each satisfying this. -/
private theorem cobsig_lin_sub_dvd (l : List (List ℤ × Data.V3)) (lam : List ℤ)
    (A : Data.M3) (n : ℤ)
    (hrow : ∀ p ∈ l, Data.V3.dvd n (Data.V3.sub p.2 (Data.M3.mulV A p.2)) = true) :
    Data.V3.dvd n (Data.V3.sub (Data.lin (l.map Prod.snd) lam)
      (Data.M3.mulV A (Data.lin (l.map Prod.snd) lam))) = true := by
  induction l generalizing lam with
  | nil =>
      rw [List.map_nil, show Data.lin ([] : List Data.V3) lam = Data.V3.zero from rfl,
        cobsig_mulV_zero, cobsig_sub_self, cobsig_dvd_zero]
  | cons p ps ih =>
      cases lam with
      | nil =>
          rw [List.map_cons, show Data.lin (p.2 :: ps.map Prod.snd) [] = Data.V3.zero from rfl,
            cobsig_mulV_zero, cobsig_sub_self, cobsig_dvd_zero]
      | cons c cs =>
          have hrow' : ∀ q ∈ ps, Data.V3.dvd n (Data.V3.sub q.2 (Data.M3.mulV A q.2)) = true :=
            fun q hq => hrow q (List.mem_cons_of_mem p hq)
          have hp : Data.V3.dvd n (Data.V3.sub p.2 (Data.M3.mulV A p.2)) = true :=
            hrow p List.mem_cons_self
          rw [List.map_cons,
            show Data.lin (p.2 :: ps.map Prod.snd) (c :: cs)
              = Data.V3.add (Data.V3.smul c p.2) (Data.lin (ps.map Prod.snd) cs) from rfl,
            cobsig_lin_decomp A c p.2 (Data.lin (ps.map Prod.snd) cs)]
          exact cobsig_dvd_add (cobsig_dvd_smul c hp) (ih cs hrow')

/-- Division commutes with the `lam`-combination of divisible vectors. -/
private theorem cobsig_lin_ediv (l : List (List ℤ × Data.V3)) (lam : List ℤ)
    (A : Data.M3) (n : ℤ)
    (hrow : ∀ p ∈ l, Data.V3.dvd n (Data.V3.sub p.2 (Data.M3.mulV A p.2)) = true) :
    Data.V3.ediv (Data.V3.sub (Data.lin (l.map Prod.snd) lam)
        (Data.M3.mulV A (Data.lin (l.map Prod.snd) lam))) n
      = Data.lin (l.map (fun p => Data.V3.ediv (Data.V3.sub p.2 (Data.M3.mulV A p.2)) n)) lam := by
  induction l generalizing lam with
  | nil =>
      rw [List.map_nil, show Data.lin ([] : List Data.V3) lam = Data.V3.zero from rfl,
        cobsig_mulV_zero, cobsig_sub_self, cobsig_ediv_zero]
      rfl
  | cons p ps ih =>
      cases lam with
      | nil =>
          rw [List.map_cons, show Data.lin (p.2 :: ps.map Prod.snd) [] = Data.V3.zero from rfl,
            cobsig_mulV_zero, cobsig_sub_self, cobsig_ediv_zero]
          rfl
      | cons c cs =>
          have hrow' : ∀ q ∈ ps, Data.V3.dvd n (Data.V3.sub q.2 (Data.M3.mulV A q.2)) = true :=
            fun q hq => hrow q (List.mem_cons_of_mem p hq)
          have hp : Data.V3.dvd n (Data.V3.sub p.2 (Data.M3.mulV A p.2)) = true :=
            hrow p List.mem_cons_self
          rw [List.map_cons,
            show Data.lin (p.2 :: ps.map Prod.snd) (c :: cs)
              = Data.V3.add (Data.V3.smul c p.2) (Data.lin (ps.map Prod.snd) cs) from rfl,
            cobsig_lin_decomp A c p.2 (Data.lin (ps.map Prod.snd) cs),
            cobsig_ediv_add (cobsig_dvd_smul c hp), cobsig_ediv_smul c hp, ih cs hrow']
          rfl

/-! ## `Data.cobVec` and `RC.yvec` coordinates -/

private theorem cobsig_cobVec_eq_unblocks (D : Data.ArithData) (n : ℤ) (σ : Data.V3) :
    Data.cobVec D n σ
      = Data.unblocks (D.gens.map (fun g =>
          Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV g σ)) n)) := by
  rw [Data.cobVec, Data.unblocks, List.flatMap_map]

private theorem cobsig_cobVec_len (D : Data.ArithData) (n : ℤ) (σ : Data.V3) :
    (Data.cobVec D n σ).length = 3 * D.gens.length := by
  rw [cobsig_cobVec_eq_unblocks, cobsig_unblocks_length, List.length_map]

private theorem cobsig_cobVec_getD (D : Data.ArithData) (n : ℤ) (σ : Data.V3) (g : ℕ)
    (hg : g < D.gens.length) (c : Fin 3) :
    (Data.cobVec D n σ).getD (3 * g + c.val) 0 =
      (Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV (D.gens.getD g Data.M3.one) σ)) n).toFun c := by
  rw [cobsig_cobVec_eq_unblocks, cobsig_unblocks_getD _ g c (by rw [List.length_map]; exact hg)]
  congr 1
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hg), List.getElem_map,
    List.getD_eq_getElem _ _ hg]

private theorem cobsig_yvec_len (j : Fin 73) (z : ℕ → Fin 3 → ℤ) :
    (RC.yvec j z).length = RC.N3 j := by
  rw [RC.yvec, cobsig_unblocks_length, List.length_map, List.length_range, RC.N3]

private theorem cobsig_yvec_getD (j : Fin 73) (z : ℕ → Fin 3 → ℤ) (g : ℕ)
    (hg : g < RC.KK j) (c : Fin 3) :
    (RC.yvec j z).getD (3 * g + c.val) 0 = z (RC.geni j g) c := by
  have hlen : 3 * (g + 1) ≤ (RC.yvec j z).length := by rw [cobsig_yvec_len, RC.N3]; omega
  rw [← cobsig_blk_toFun (RC.yvec j z) g c hlen, RC.blocks_yvec j z g hg, CZ.ofFun_toFun]

private theorem cobsig_cz_geni (j : Fin 73) (σ : Data.V3) (g : ℕ) (hg : g < RC.KK j) :
    RC.cz j σ (RC.geni j g)
      = fun c => (Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV (RC.gMt j g) σ))
          ((RC.Ad j).n)).toFun c := by
  have hgen : RC.eM j (RC.geni j g) = RC.gMt j g := by
    simp only [RC.eM, RC.gMt, RC.geni]
    exact RC.Ad_genIdx_rel j g (by simpa only [RC.KK] using hg)
  funext c; simp only [RC.cz, hgen]

/-! ## List-sum divisibility glue -/

private theorem cobsig_sum_map_sub {α : Type*} (l : List α) (f g : α → ℤ) :
    (l.map f).sum - (l.map g).sum = (l.map (fun x => f x - g x)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

private theorem cobsig_dvd_sum_map {α : Type*} (l : List α) (f : α → ℤ) (n : ℤ)
    (h : ∀ x ∈ l, n ∣ f x) : n ∣ (l.map f).sum :=
  List.dvd_sum (fun x hx => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact h c hc)

private theorem cobsig_modsum (n : ℤ) (m : ℕ) (cs : List ℤ) (a b : ℕ → ℤ)
    (h : ∀ c, c < m → n ∣ a c - b c) :
    n ∣ ((List.range m).map (fun c => cs.getD c 0 * a c)).sum -
      ((List.range m).map (fun c => cs.getD c 0 * b c)).sum := by
  rw [cobsig_sum_map_sub]
  refine cobsig_dvd_sum_map _ _ n (fun c hc => ?_)
  rw [List.mem_range] at hc
  rw [← mul_sub]
  exact dvd_mul_of_dvd_right (h c hc) _

theorem RepCoh_cobsig (j : Fin 73) (h : ℕ) (hh : h < (Work.SG.RC.Cd j).reps.length)
    (y lam : List ℤ) (hy : y.length = Work.SG.RC.N3 j)
    (hlam : ∀ q, q < Work.SG.RC.N3 j →
      (Work.SG.RC.vsub y ((Work.SG.RC.Cd j).reps.getD h [])).getD q 0
        = Work.SG.RC.linC (Work.SG.RC.BlR (Work.SG.RC.Cd j).Bl) lam q) :
    ∃ σ : Data.V3,
      (∀ g, g < Work.SG.RC.KK j → Data.V3.dvd ((Work.SG.RC.Ad j).n)
        (Data.V3.sub σ (Data.M3.mulV (Work.SG.RC.gMt j g) σ)) = true) ∧
      (∀ q, q < Work.SG.RC.N3 j →
        ((Work.SG.RC.vsub y ((Work.SG.RC.Cd j).reps.getD h [])).getD q 0
          - (Work.SG.RC.yvec j (Work.SG.RC.cz j σ)).getD q 0) % ((Work.SG.RC.Ad j).n : ℤ) = 0) := by
  have hn0 : ((RC.Ad j).n : ℤ) ≠ 0 := by have := RC.N_pos j; omega
  have hBl_len : (RC.Cd j).Bl.length = RC.N3 j := RC.Cd_Bl_len j
  have hrep_len : ((RC.Cd j).reps.getD h []).length = RC.N3 j := by
    rw [List.getD_eq_getElem _ _ hh]
    exact (RC.Cd_reps_red j _ (List.getElem_mem hh)).1
  -- the certified divisibility attached to every row of `Bl`, for a fixed generator `g`
  have hrowOf : ∀ (g : ℕ), g < RC.KK j →
      ∀ p ∈ (RC.Cd j).Bl,
        Data.V3.dvd ((RC.Ad j).n) (Data.V3.sub p.2 (Data.M3.mulV (RC.gMt j g) p.2)) = true := by
    intro g hg p hp
    have hg' : g < (RC.Ad j).gens.length := by simpa only [RC.KK] using hg
    have hgens : RC.gMt j g ∈ (RC.Ad j).gens := by
      simp only [RC.gMt]
      rw [List.getD_eq_getElem _ _ hg']
      exact List.getElem_mem hg'
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    have hi' : i < RC.N3 j := by rw [← hBl_len]; exact hi
    have h2 := RC.Cd_Bl_sig j i hi' (RC.gMt j g) hgens
    simp only [RC.BlRow] at h2
    rwa [List.getD_eq_getElem (RC.Cd j).Bl ([], Data.V3.zero) hi] at h2
  refine ⟨Data.lin ((RC.Cd j).Bl.map Prod.snd) lam, ?_, ?_⟩
  · intro g hg
    exact cobsig_lin_sub_dvd (RC.Cd j).Bl lam (RC.gMt j g) ((RC.Ad j).n) (hrowOf g hg)
  · intro q hq
    obtain ⟨g, c, rfl⟩ : ∃ (g : ℕ) (c : Fin 3), q = 3 * g + c.val :=
      ⟨q / 3, ⟨q % 3, Nat.mod_lt _ (by norm_num)⟩, (Nat.div_add_mod q 3).symm⟩
    have hgK : g < RC.KK j := by
      show g < (RC.Ad j).gens.length
      rw [RC.N3, RC.KK] at hq
      have := c.isLt
      omega
    have hg' : g < (RC.Ad j).gens.length := by simpa only [RC.KK] using hgK
    have hrow := hrowOf g hgK
    set σ : Data.V3 := Data.lin ((RC.Cd j).Bl.map Prod.snd) lam with hσdef
    have hvsub : (RC.vsub y ((RC.Cd j).reps.getD h [])).getD (3 * g + c.val) 0
        = y.getD (3 * g + c.val) 0
          - ((RC.Cd j).reps.getD h []).getD (3 * g + c.val) 0 :=
      RC.vsub_getD hy hrep_len (3 * g + c.val) hq
    have hmid : y.getD (3 * g + c.val) 0
          - ((RC.Cd j).reps.getD h []).getD (3 * g + c.val) 0
        = RC.linC (RC.BlR (RC.Cd j).Bl) lam (3 * g + c.val) := by
      rw [← hvsub]; exact hlam _ hq
    have hlinC : RC.linC (RC.BlR (RC.Cd j).Bl) lam (3 * g + c.val)
        = ((List.range (RC.Cd j).Bl.length).map (fun i =>
            lam.getD i 0 * ((RC.Cd j).Bl.getD i ([], Data.V3.zero)).1.getD
              (3 * g + c.val) 0)).sum := by
      simp only [RC.linC, RC.BlR_length, RC.BlR_getD]
    have hyvec : (RC.yvec j (RC.cz j σ)).getD (3 * g + c.val) 0
        = (Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV (RC.gMt j g) σ))
            ((RC.Ad j).n)).toFun c := by
      rw [cobsig_yvec_getD j (RC.cz j σ) g hgK c, cobsig_cz_geni j σ g hgK]
    have hE : Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV (RC.gMt j g) σ)) ((RC.Ad j).n)
        = Data.lin ((RC.Cd j).Bl.map (fun p =>
            Data.V3.ediv (Data.V3.sub p.2 (Data.M3.mulV (RC.gMt j g) p.2)) ((RC.Ad j).n))) lam := by
      rw [hσdef]
      exact cobsig_lin_ediv (RC.Cd j).Bl lam (RC.gMt j g) ((RC.Ad j).n) hrow
    set Ef : ℕ → Data.V3 := fun i => Data.V3.ediv (Data.V3.sub
        ((RC.Cd j).Bl.getD i ([], Data.V3.zero)).2
        (Data.M3.mulV (RC.gMt j g) ((RC.Cd j).Bl.getD i ([], Data.V3.zero)).2))
        ((RC.Ad j).n) with hEfdef
    have hEapp : (Data.V3.ediv (Data.V3.sub σ (Data.M3.mulV (RC.gMt j g) σ))
          ((RC.Ad j).n)).toFun c
        = ((List.range (RC.Cd j).Bl.length).map (fun i => lam.getD i 0 * (Ef i).toFun c)).sum := by
      rw [hE, cobsig_lin_toFun]
      rw [show (List.map (fun p => Data.V3.ediv (Data.V3.sub p.2
            (Data.M3.mulV (RC.gMt j g) p.2)) ((RC.Ad j).n)) (RC.Cd j).Bl).length
          = (RC.Cd j).Bl.length from by rw [List.length_map]]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      simp only [hEfdef]
      rw [cobsig_getD_map (RC.Cd j).Bl (fun p => Data.V3.ediv (Data.V3.sub p.2
        (Data.M3.mulV (RC.gMt j g) p.2)) ((RC.Ad j).n)) ([], Data.V3.zero) Data.V3.zero i hi]
    have hrowdiv : ∀ i, i < (RC.Cd j).Bl.length →
        ((RC.Ad j).n : ℤ) ∣ ((RC.Cd j).Bl.getD i ([], Data.V3.zero)).1.getD
            (3 * g + c.val) 0 - (Ef i).toFun c := by
      intro i hi
      have hi' : i < RC.N3 j := by rw [← hBl_len]; exact hi
      have hzb := RC.Cd_Bl_cob j i hi'
      have hlen1 : 3 * g + c.val < ((RC.BlRow j i).1).length := by
        rw [RC.Cd_Bl_rowlen j i hi']; exact hq
      have hlen2 : 3 * g + c.val
          < (Data.cobVec (RC.Ad j) ((RC.Ad j).n) (RC.BlRow j i).2).length := by
        rw [cobsig_cobVec_len]
        show 3 * g + c.val < 3 * (RC.Ad j).gens.length
        rw [RC.N3, RC.KK] at hq; exact hq
      have h1 : (((RC.BlRow j i).1.getD (3 * g + c.val) 0)
          - ((Data.cobVec (RC.Ad j) ((RC.Ad j).n) (RC.BlRow j i).2).getD
              (3 * g + c.val) 0)) % ((RC.Ad j).n : ℤ) = 0 :=
        beq_iff_eq.mp (RC.zipWith_coord hzb hlen1 hlen2)
      have h2 : (Data.cobVec (RC.Ad j) ((RC.Ad j).n) (RC.BlRow j i).2).getD
            (3 * g + c.val) 0 = (Ef i).toFun c := by
        rw [cobsig_cobVec_getD (RC.Ad j) ((RC.Ad j).n) (RC.BlRow j i).2 g hg' c]
        simp only [RC.BlRow, hEfdef, RC.gMt]
      have h3 : ((RC.Ad j).n : ℤ) ∣ (RC.BlRow j i).1.getD (3 * g + c.val) 0
          - (Data.cobVec (RC.Ad j) ((RC.Ad j).n) (RC.BlRow j i).2).getD
              (3 * g + c.val) 0 := Int.dvd_of_emod_eq_zero h1
      rw [h2] at h3
      simpa only [RC.BlRow] using h3
    have hsumdiv := cobsig_modsum ((RC.Ad j).n) (RC.Cd j).Bl.length lam
      (fun i => ((RC.Cd j).Bl.getD i ([], Data.V3.zero)).1.getD (3 * g + c.val) 0)
      (fun i => (Ef i).toFun c) hrowdiv
    rw [hvsub, hmid, hlinC, hyvec, hEapp]
    exact Int.dvd_iff_emod_eq_zero.mp hsumdiv

end Work.SG
