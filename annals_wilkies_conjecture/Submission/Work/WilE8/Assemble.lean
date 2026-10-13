/-
  WilE8 — assembling `E8_reduce` (E8a) and `E8_comps` (E8b) from the E7/E2 theorems of area E.

  The hypotheses `hCompl`/`hInter` are the frozen area-E statements `E7_star_compl` /
  `E7_star_inter` copied verbatim, and `hE2` is the frozen `E2_components` copied verbatim.
  Everything else (`StarR`-level complement/intersection/projection, the hyperplane case) is
  proved in this area.
-/
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Levels
import Submission.Work.WilE8.Reduce
import Submission.Work.WilE8.StarR.compl
import Submission.Work.WilE8.StarR.inter
import Submission.Work.WilE8.StarR.proj
import Submission.Work.WilE8.Star.init_star
import Submission.Work.WilE8.Ocube.ocube_star
import Submission.Work.WilE8.Star.card_set_le_deg_sum
import Submission.Work.WilE8.Star.preconnected_preimage_piece
import Submission.Work.WilE8.Hyp.hyp_starR

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology
namespace Work.WilE8
open WilkiesDesign WilkiesDesign.E

/-- The `Star`-level projection fact, in the exact shape `StarR.proj` expects. -/
lemma star_init_proj {N F D : ℕ} {Z : Set (Fin (N + 1) → ℝ)} (h : Star F D (N + 1) Z) :
    Star F D N (Fin.init '' Z) :=
  (Star.init_star h).1

/-- The `ocube` fact, in the exact shape `StarR.proj` expects. -/
lemma ocube_star' (N : ℕ) : Star N (2 * N + 1) N (ocube N) := Ocube.ocube_star N

/-- The closure data of `Levels.lean`, assembled from the E7/E2 statements of area E. -/
noncomputable def closeOf
    (hCompl : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (Y : Set (Fin n → ℝ)),
      Star F D n Y → Star a (p.eval D) n (cubeC n \ Y))
    (hInter : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (k : ℕ) (D : Fin k → ℕ)
      (Y : Fin k → Set (Fin n → ℝ)), (∀ i, Star F (D i) n (Y i)) →
      Star a (p.eval (∑ i, D i)) n (cubeC n ∩ ⋂ i, Y i))
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y) :
    Close where
  complA := fun a0 n => (StarR.compl hCompl a0 n).choose
  complP := fun a0 n => (StarR.compl hCompl a0 n).choose_spec.choose
  hcompl := fun a0 n => (StarR.compl hCompl a0 n).choose_spec.choose_spec
  interA := fun a0 n => (StarR.inter hInter a0 n).choose
  interP := fun a0 n => (StarR.inter hInter a0 n).choose_spec.choose
  hinter := fun a0 n => (StarR.inter hInter a0 n).choose_spec.choose_spec
  projA := fun a0 n =>
    (StarR.proj hInter (fun h => star_init_proj h) ocube_star' a0 n).choose
  projP := fun a0 n =>
    (StarR.proj hInter (fun h => star_init_proj h) ocube_star' a0 n).choose_spec.choose
  hproj := fun a0 n =>
    (StarR.proj hInter (fun h => star_init_proj h) ocube_star' a0 n).choose_spec.choose_spec
  hypP := fun n => (Hyp.hyp_starR hE2 n).choose
  hhyp := fun n Q hQ => (Hyp.hyp_starR hE2 n).choose_spec Q hQ

/-- **E8a.** Reduction `Gen ≤ StarR` (2209.10972 Def. 1.4 style). -/
theorem E8_reduce_proved
    (hCompl : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (Y : Set (Fin n → ℝ)),
      Star F D n Y → Star a (p.eval D) n (cubeC n \ Y))
    (hInter : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (k : ℕ) (D : Fin k → ℕ)
      (Y : Fin k → Set (Fin n → ℝ)), (∀ i, Star F (D i) n (Y i)) →
      Star a (p.eval (∑ i, D i)) n (cubeC n ∩ ⋂ i, Y i))
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y) :
    ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), p.eval 0 = 0 ∧
      ∀ (D : ℕ) (X : Set (Fin n → ℝ)), Gen F D n X → StarR a (p.eval D) n X := by
  intro F n
  exact ⟨(closeOf hCompl hInter hE2).lvlA F n, (closeOf hCompl hInter hE2).lvlP F n,
    (closeOf hCompl hInter hE2).lvlP_eval_zero F n,
    fun D X hX => (closeOf hCompl hInter hE2).reduce_core F D n X hX⟩

/-- **E8b.** SOMin axiom 4. -/
theorem E8_comps_proved
    (hCompl : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (Y : Set (Fin n → ℝ)),
      Star F D n Y → Star a (p.eval D) n (cubeC n \ Y))
    (hInter : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (k : ℕ) (D : Fin k → ℕ)
      (Y : Fin k → Set (Fin n → ℝ)), (∀ i, Star F (D i) n (Y i)) →
      Star a (p.eval (∑ i, D i)) n (cubeC n ∩ ⋂ i, Y i))
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y) :
    ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (D : ℕ) (A : Set (Fin 1 → ℝ)), Gen F D 1 A →
      ∃ s : Finset (Set (Fin 1 → ℝ)), s.card ≤ p.eval D ∧ (∀ c ∈ s, IsPreconnected c) ∧
        A = ⋃₀ (s : Set (Set (Fin 1 → ℝ))) := by
  intro F
  obtain ⟨a, P, hP0, hA⟩ := E8_reduce_proved hCompl hInter hE2 F 1
  refine ⟨P + Polynomial.C 2, fun D A hgen => ?_⟩
  obtain ⟨Z, hZ, hAZ⟩ := hA D A hgen
  obtain ⟨L, hL, -, hdeg⟩ := hZ
  refine ⟨((L.map fun Q => Q.set).toFinset).image (fun S => psiV ⁻¹' S), ?_, ?_, ?_⟩
  · refine le_trans (Finset.card_image_le) ?_
    refine le_trans (Star.card_set_le_deg_sum L) ?_
    have h := Poly.eval_mono_nat P (Nat.le_add_right D 2)
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega
  · intro c hc
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hc
    rw [List.mem_toFinset] at hS
    obtain ⟨Q, -, rfl⟩ := List.mem_map.mp hS
    exact Star.preconnected_preimage_piece Q
  · rw [hAZ, hL]
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      rw [Set.mem_preimage] at hx
      rw [mem_list_iUnion] at hx
      obtain ⟨Q, hQ, hxQ⟩ := hx
      refine ⟨psiV ⁻¹' Q.set, ?_, hxQ⟩
      refine Finset.mem_image.mpr ⟨Q.set, ?_, rfl⟩
      rw [List.mem_toFinset]
      exact List.mem_map_of_mem hQ
    · intro x hx
      rw [Set.mem_sUnion] at hx
      obtain ⟨T, hT, hxT⟩ := hx
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      rw [List.mem_toFinset] at hS
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hS
      rw [Set.mem_preimage]
      rw [mem_list_iUnion]
      exact ⟨Q, hQ, hxT⟩

end Work.WilE8
