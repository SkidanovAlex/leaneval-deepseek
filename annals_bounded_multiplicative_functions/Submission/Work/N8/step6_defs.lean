import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared definitions and combinatorial lemmas for the Step-6 `q₀`-bound

(`Work.N8.step6_q0_bound`)

* `step6next ℓ j`: the successor of `j` in a cyclic walk of length `ℓ`;
* `step6Walks Adj T ℓ`: the closed walks of length `ℓ` in the graph on `T` induced by `Adj`;
* `step6C0 ℓ = max 1 (1000·ℓ·2^ℓ)`: the (ℓ-dependent) window constant fed to `hN4`;
* `step6Ab k ℓ c₂ G Ck`: the explicit constant `Abound` of the theorem;
* `chainSet`, `succ_card_le`, `chain_fiber_card`, `chain_card_le`: the combinatorial core of the
  upper bound for the number of closed walks (each step has at most `K` admissible successors).
-/

namespace Work.N8

open Finset

/-- The successor index of `j` in a cyclic walk of length `ℓ`. -/
def step6next (ℓ : ℕ) (j : Fin ℓ) : Fin ℓ :=
  ⟨((j : ℕ) + 1) % ℓ, Nat.mod_lt _ j.pos⟩

@[simp] lemma step6next_val (ℓ : ℕ) (j : Fin ℓ) :
    ((step6next ℓ j : Fin ℓ) : ℕ) = ((j : ℕ) + 1) % ℓ := rfl

/-- The closed walks of length `ℓ` in the graph on `T` induced by `Adj`: the functions
`w : Fin ℓ → V` with all values in `T` and `Adj (w j) (w (j+1))` cyclically. -/
def step6Walks {V : Type} [Fintype V] [DecidableEq V] (Adj : V → V → Prop) [DecidableRel Adj]
    (T : Finset V) (ℓ : ℕ) : Finset (Fin ℓ → V) :=
  Finset.univ.filter (fun w => (∀ j, w j ∈ T) ∧ (∀ j, Adj (w j) (w (step6next ℓ j))))

lemma mem_step6Walks {V : Type} [Fintype V] [DecidableEq V] {Adj : V → V → Prop}
    [DecidableRel Adj] {T : Finset V} {ℓ : ℕ} {w : Fin ℓ → V} :
    w ∈ step6Walks Adj T ℓ ↔ (∀ j, w j ∈ T) ∧ (∀ j, Adj (w j) (w (step6next ℓ j))) := by
  simp [step6Walks]

/-- The window constant `C₀(ℓ) = max 1 (1000·ℓ·2^ℓ)`. -/
noncomputable def step6C0 (ℓ : ℕ) : ℝ := max 1 (1000 * (ℓ : ℝ) * (2 : ℝ) ^ ℓ)

lemma one_le_step6C0 (ℓ : ℕ) : 1 ≤ step6C0 ℓ := le_max_left _ _

lemma step6C0_nonneg (ℓ : ℕ) : 0 ≤ step6C0 ℓ := le_trans zero_le_one (one_le_step6C0 ℓ)

lemma le_step6C0 (ℓ : ℕ) : 1000 * (ℓ : ℝ) * (2 : ℝ) ^ ℓ ≤ step6C0 ℓ := le_max_right _ _

/-- The explicit constant `Abound` of `step6_q0_bound`, positive for every argument. -/
noncomputable def step6Ab (k ℓ : ℕ) (c₂ G Ck : ℝ) : ℝ :=
  (|c₂| + 1) * (|G| + 1) * step6C0 ℓ * (|Ck| * (k.factorial : ℝ) + 1) * (2 * (k : ℝ) + 1)

lemma step6Ab_pos (k ℓ : ℕ) (c₂ G Ck : ℝ) : 0 < step6Ab k ℓ c₂ G Ck := by
  have h1 : (0:ℝ) < step6C0 ℓ := lt_of_lt_of_le one_pos (one_le_step6C0 ℓ)
  have h2 : (0:ℝ) < |c₂| + 1 := by positivity
  have h3 : (0:ℝ) < |G| + 1 := by positivity
  have h4 : (0:ℝ) < |Ck| * (k.factorial : ℝ) + 1 := by positivity
  have h5 : (0:ℝ) < 2 * (k:ℝ) + 1 := by positivity
  unfold step6Ab
  positivity

/-! ## The successor bound -/

/-- All the successors of `x` carrying a fixed prime pair lie in a single `pos`-fiber: the
geometry window `|pos x - (b/a)·pos y| ≤ 100 L` with `a ≤ 2P`, `b ≥ P` has length
`≤ 400 L < 500 L`, and `pos` is `500 L`-separated. -/
lemma succ_card_le {V : Type} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) [DecidableRel Adj] (T : Finset V) (pos : V → ℝ) (pr : V → V → ℕ × ℕ)
    (P L : ℝ) (hP : 1 ≤ P) (hL : 0 < L) (K : ℕ)
    (hpr : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' → Work.BMF.IsPrimeIn P (2 * P) (pr v v').1 ∧
        Work.BMF.IsPrimeIn P (2 * P) (pr v v').2)
    (hfib : ∀ y : ℝ, ((T.filter (fun v ↦ pos v = y)).card : ℝ) ≤ (K : ℝ))
    (hsep : ∀ v ∈ T, ∀ v' ∈ T, pos v ≠ pos v' → 500 * L ≤ |pos v - pos v'|)
    (hgeo : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      |pos v - (((pr v v').2 : ℕ) : ℝ) / (((pr v v').1 : ℕ) : ℝ) * pos v'| ≤ 100 * L)
    (x : V) (hxT : x ∈ T) (a b : ℕ) :
    ((T.filter (fun y ↦ Adj x y ∧ (pr x y).1 = a ∧ (pr x y).2 = b)).card : ℝ) ≤ (K : ℝ) := by
  classical
  set Sx : Finset V := T.filter (fun y ↦ Adj x y ∧ (pr x y).1 = a ∧ (pr x y).2 = b) with hSx
  rcases Sx.eq_empty_or_nonempty with hE | ⟨y₀, hy₀⟩
  · rw [hE]; simp
  · have hmem : ∀ y ∈ Sx, y ∈ T ∧ Adj x y ∧ (pr x y).1 = a ∧ (pr x y).2 = b :=
      fun y hy => Finset.mem_filter.mp hy
    have hsame : ∀ y ∈ Sx, pos y = pos y₀ := by
      intro y hy
      obtain ⟨hyT, hAy, ha1, hb1⟩ := hmem y hy
      obtain ⟨hy0T, hAy0, ha0, hb0⟩ := hmem y₀ hy₀
      have haP : P ≤ (a : ℝ) := by rw [← ha1]; exact (hpr x hxT y hyT hAy).1.2.1
      have hbP : P ≤ (b : ℝ) := by rw [← hb1]; exact (hpr x hxT y hyT hAy).2.2.1
      have ha2P : (a : ℝ) ≤ 2 * P := by rw [← ha1]; exact (hpr x hxT y hyT hAy).1.2.2
      have hPpos : (0:ℝ) < P := lt_of_lt_of_le zero_lt_one hP
      have hapos : (0:ℝ) < (a:ℝ) := lt_of_lt_of_le hPpos haP
      have hbpos : (0:ℝ) < (b:ℝ) := lt_of_lt_of_le hPpos hbP
      have hratpos : (0:ℝ) < (b:ℝ)/(a:ℝ) := div_pos hbpos hapos
      have hratio : (1:ℝ)/2 ≤ (b:ℝ)/(a:ℝ) := by
        rw [le_div_iff₀ hapos]; linarith
      have hpy := hgeo x hxT y hyT hAy
      have hpy0 := hgeo x hxT y₀ hy0T hAy0
      rw [hb1, ha1] at hpy
      rw [hb0, ha0] at hpy0
      have h3 : |pos y * ((b:ℝ)/(a:ℝ)) - pos x| ≤ 100 * L := by
        rw [abs_sub_comm, mul_comm]; exact hpy
      have h4 : |pos x - pos y₀ * ((b:ℝ)/(a:ℝ))| ≤ 100 * L := by
        rw [mul_comm]; exact hpy0
      have hkey : |pos y * ((b:ℝ)/(a:ℝ)) - pos y₀ * ((b:ℝ)/(a:ℝ))| ≤ 200 * L := by
        have := abs_sub_le (pos y * ((b:ℝ)/(a:ℝ))) (pos x) (pos y₀ * ((b:ℝ)/(a:ℝ)))
        linarith
      have he : |pos y - pos y₀| * ((b:ℝ)/(a:ℝ))
          = |pos y * ((b:ℝ)/(a:ℝ)) - pos y₀ * ((b:ℝ)/(a:ℝ))| := by
        rw [← sub_mul, abs_mul, abs_of_pos hratpos]
      have hfin : |pos y - pos y₀| ≤ 400 * L := by
        have h5 : |pos y - pos y₀| * ((1:ℝ)/2) ≤ |pos y - pos y₀| * ((b:ℝ)/(a:ℝ)) :=
          mul_le_mul_of_nonneg_left hratio (abs_nonneg _)
        rw [he] at h5
        nlinarith [hkey, h5]
      by_contra hne
      have h6 := hsep y hyT y₀ hy0T hne
      linarith
    have hsub : Sx ⊆ T.filter (fun v ↦ pos v = pos y₀) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨(hmem y hy).1, hsame y hy⟩
    calc (Sx.card : ℝ) ≤ ((T.filter (fun v ↦ pos v = pos y₀)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (K : ℝ) := hfib (pos y₀)

/-! ## Chains of successors -/

/-- The chains of length `m` in the graph whose `j`-th step goes from `u j` to `u (j+1)` and
must land in the set `S j (u j)`, with the first vertex pinned to `v₀`. -/
noncomputable def chainSet {V : Type} [Fintype V] [DecidableEq V] (m : ℕ) (v₀ : V)
    (S : Fin m → V → Finset V) : Finset (Fin m → V) := by
  classical
  exact Finset.univ.filter (fun u => (∀ h : 0 < m, u ⟨0, h⟩ = v₀) ∧
    ∀ (j : Fin m) (hj : (j : ℕ) + 1 < m),
      u ⟨(j : ℕ) + 1, hj⟩ ∈ S j (u j))

/-- The fibre of the restriction map on `chainSet`, when each step set has at most `K`
elements. -/
lemma chain_fiber_card {V : Type} [Fintype V] [DecidableEq V] (m : ℕ) (v₀ : V)
    (S : Fin (m+1) → V → Finset V) (K : ℕ) (hK : 1 ≤ K)
    (hS : ∀ (j : Fin (m+1)) (x : V), (S j x).card ≤ K)
    (w : Fin (m+1) → V) :
    (((chainSet (m+1) v₀ S).filter
        (fun u => (fun j : Fin m => u j.castSucc) = (fun j : Fin m => w j.castSucc))).card) ≤ K := by
  classical
  rcases m with _ | m'
  · have h1 : (chainSet 1 v₀ S).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' : a ⟨0, Nat.succ_pos 0⟩ = v₀ := by
        have h := ha; rw [chainSet, Finset.mem_filter] at h; exact h.2.1 (Nat.succ_pos 0)
      have hb' : b ⟨0, Nat.succ_pos 0⟩ = v₀ := by
        have h := hb; rw [chainSet, Finset.mem_filter] at h; exact h.2.1 (Nat.succ_pos 0)
      funext i
      have hi : i = ⟨0, Nat.succ_pos 0⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
      rw [hi, ha', hb']
    exact le_trans (le_trans (Finset.card_le_card (Finset.filter_subset _ _)) h1) hK
  · have hm1 : m' < m' + 2 := by omega
    have hm2 : m' + 1 < m' + 2 := by omega
    set φ : (Fin (m'+2) → V) → V := fun u => u ⟨m'+1, hm2⟩ with hφ
    have hφmem : ∀ u ∈ (chainSet (m'+2) v₀ S).filter
        (fun u => (fun j : Fin (m'+1) => u j.castSucc) = (fun j : Fin (m'+1) => w j.castSucc)),
        φ u ∈ S ⟨m', hm1⟩ (w ⟨m', hm1⟩) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨huA, huR⟩ := hu
      have hcon := huA
      rw [chainSet, Finset.mem_filter] at hcon
      have hstep := hcon.2.2 ⟨m', hm1⟩ (by simpa using hm2)
      have hlast : u ⟨m', hm1⟩ = w ⟨m', hm1⟩ :=
        congrFun huR (⟨m', Nat.lt_succ_self m'⟩ : Fin (m'+1))
      rw [hlast] at hstep
      exact hstep
    have hinj : ∀ a ∈ (chainSet (m'+2) v₀ S).filter
        (fun u => (fun j : Fin (m'+1) => u j.castSucc) = (fun j : Fin (m'+1) => w j.castSucc)),
        ∀ b ∈ (chainSet (m'+2) v₀ S).filter
        (fun u => (fun j : Fin (m'+1) => u j.castSucc) = (fun j : Fin (m'+1) => w j.castSucc)),
        φ a = φ b → a = b := by
      intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      funext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have h1 := congrFun ha.2 j
        have h2 := congrFun hb.2 j
        rw [h1, h2]
      · exact hab
    have hcard := Finset.card_le_card_of_injOn φ hφmem hinj
    exact le_trans hcard (hS ⟨m', hm1⟩ (w ⟨m', hm1⟩))

/-- A chain with at most `K` successors per step has at most `K ^ m` members. -/
lemma chain_card_le {V : Type} [Fintype V] [DecidableEq V] (m : ℕ) :
    ∀ (v₀ : V) (S : Fin m → V → Finset V) (K : ℕ), 1 ≤ K →
      (∀ (j : Fin m) (x : V), (S j x).card ≤ K) →
      ((chainSet m v₀ S).card : ℝ) ≤ (K : ℝ)^m := by
  induction m with
  | zero =>
      intro v₀ S K hK hS
      haveI : Subsingleton (Fin 0 → V) := ⟨fun f g => funext (fun i => i.elim0)⟩
      have h1 : (chainSet 0 v₀ S).card ≤ 1 :=
        Finset.card_le_one.mpr (fun a _ b _ => Subsingleton.elim a b)
      calc ((chainSet 0 v₀ S).card : ℝ) ≤ 1 := by exact_mod_cast h1
        _ = (K : ℝ)^0 := by simp
  | succ m ih =>
      intro v₀ S K hK hS
      have himg : (chainSet (m+1) v₀ S).image
            (fun u : Fin (m+1) → V => fun j : Fin m => u j.castSucc)
          ⊆ chainSet m v₀ (fun j : Fin m => S j.castSucc) := by
        intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨u, hu, rfl⟩ := hv
        simp only [chainSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        exact ⟨fun h => hu.1 (Nat.lt_trans h (Nat.lt_succ_self m)),
               fun (j : Fin m) hj => hu.2 j.castSucc (by simpa using hj)⟩
      have hfib : ∀ b ∈ (chainSet (m+1) v₀ S).image
            (fun u : Fin (m+1) → V => fun j : Fin m => u j.castSucc),
          (((chainSet (m+1) v₀ S).filter
            (fun u => (fun j : Fin m => u j.castSucc) = b)).card) ≤ K := by
        intro b hb
        rw [Finset.mem_image] at hb
        obtain ⟨w, -, rfl⟩ := hb
        exact chain_fiber_card m v₀ S K hK hS w
      have h1 : (chainSet (m+1) v₀ S).card
          ≤ K * ((chainSet (m+1) v₀ S).image
              (fun u : Fin (m+1) → V => fun j : Fin m => u j.castSucc)).card :=
        Finset.card_le_mul_card_image _ K hfib
      have h2 : ((chainSet (m+1) v₀ S).image
              (fun u : Fin (m+1) → V => fun j : Fin m => u j.castSucc)).card
          ≤ (chainSet m v₀ (fun j : Fin m => S j.castSucc)).card := Finset.card_le_card himg
      have h3 : ((chainSet m v₀ (fun j : Fin m => S j.castSucc)).card : ℝ) ≤ (K:ℝ)^m :=
        ih v₀ (fun j : Fin m => S j.castSucc) K hK (fun j x => hS j.castSucc x)
      calc ((chainSet (m+1) v₀ S).card : ℝ)
          ≤ (K:ℝ) * (((chainSet (m+1) v₀ S).image
              (fun u : Fin (m+1) → V => fun j : Fin m => u j.castSucc)).card : ℝ) := by
            exact_mod_cast h1
        _ ≤ (K:ℝ) * ((chainSet m v₀ (fun j : Fin m => S j.castSucc)).card : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact_mod_cast h2
        _ ≤ (K:ℝ) * (K:ℝ)^m := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (K:ℝ)^(m+1) := by ring

end Work.N8
