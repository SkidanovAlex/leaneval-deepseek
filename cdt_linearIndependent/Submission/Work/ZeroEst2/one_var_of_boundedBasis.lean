import Mathlib
import Submission.Work.ZeroEst.defs
import Submission.Work.ZeroEst.one_var_defs
import Submission.Work.ZeroEst.fixed_deg_order_bound
import Submission.Work.ZeroEst.case_det_order_sum
import Submission.Work.ZeroEst.case_det_order_iter
import Submission.Work.ZeroEst.case_det_orbit_dot
import Submission.Work.ZeroEst.case_det_detdeg
import Submission.Work.ZeroEst.case_det
import Submission.Work.ZeroEst2.exists_injective_minor
import Submission.Work.ZeroEst2.order_bound_cramer
import Submission.Work.ZeroEst2.cramer_identity
import Submission.Work.ZeroEst2.orbit_rank_gen

namespace Work.ZeroEst2

open Submission.CDTPlan

/-- **Steps L1 + L3 of `REFS/NOTES_LEAD_zero_estimate.md`, given L2 as an input.**  For the
`D`-closed system `q fᵢ' = Σ Aᵢⱼ fⱼ` (`q ≠ 0`, `f` `ℚ(x)`-independent), if every `Λ`-stable
`K`-subspace `V ⊆ Kᵐ` spanned by polynomial rows (`K = ℚ(x)`, `(ΛQ)_j = q Q_j' + Σ_i Q_i A_i j`)
has a polynomial basis of `natDegree ≤ c` — the conclusion of `Work.ZeroEst3.lang24_bounded_basis`,
taken here as the hypothesis `hL2` — then Shidlovsky's one-variable bound holds:

`∃ C, ∀ D P, (∀ i, deg P i < D) → ⟨P,f⟩ ≠ 0 → ord ⟨P,f⟩ ≤ m·D + C`.

**Plan (L1 + L3 of the notes).**  Given `D` and `P`, put `Q_k = ΛᵏP` (`k ∈ ℕ`), `V_k j = Q_k j ∈ K`
and `V := K-span(V_0, …, V_{r−1})` where `r` is the *least* `k ≤ m` with `V_k ∈ span(V_0..V_{k−1})`
(exists since `V_0..V_m` are `m+1` vectors of `Kᵐ`).  Then `V_0..V_{r−1}` are `K`-independent,
`ΛV ⊆ V` (as `Λ V_k = V_{k+1}` and `V_r ∈ V`), every `V_k ∈ V`, and `r ≤ m`.  Apply `hL2` to the
generators `Q_0..Q_{r−1}`: get a basis `v_1..v_r` of `V` with `natDegree ≤ c`.  Put
`g_i := ⟨v_i, f⟩ ≠ 0` (using `PolyIndependent`), so `ord g_i ≤ N_c` for the `fixed_deg_order_bound`
constant `N_c` at degree `c`.  Each `Q_k = Σ_i λ_{k i} v_i` with `λ_{k i} ∈ K`; choosing columns `I`
with `det (v_{·I}) ≠ 0` and clearing denominators with the adjugate gives the *polynomial* matrix
identity `det(Q_{·I})·g = v_{·I}·adj(Q_{·I})·R` (with `R = (θ^k⟨P,f⟩)_k`).  Taking orders,
`ord R_0 ≤ deg det(Q_{·I}) + ord g_i + r − 1 ≤ r(D + m·δ) + N_c + r ≤ m·D + (m²δ + N_c + m)`
with `δ = dlt q A`. -/
theorem one_var_of_boundedBasis {m : ℕ} (q : Polynomial ℚ) (hq : q ≠ 0)
    (A : Fin m → Fin m → Polynomial ℚ)
    (hL2 : ∃ c : ℕ, ∀ (r : ℕ) (Q : Fin r → Fin m → Polynomial ℚ),
      LinearIndependent (RatFunc ℚ)
        (fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k j)) →
      (∀ k, (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
          (q * Polynomial.derivative (Q k j) + ∑ i, Q k i * A i j)) ∈
        Submodule.span (RatFunc ℚ)
          (Set.range fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k j))) →
      ∃ v : Fin r → Fin m → Polynomial ℚ, (∀ i j, (v i j).natDegree ≤ c) ∧
        Submodule.span (RatFunc ℚ)
            (Set.range fun i => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v i j)) =
          Submodule.span (RatFunc ℚ)
            (Set.range fun k => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k j)))
    (f : Fin m → PowerSeries ℚ) (hpi : PolyIndependent f)
    (hrel : ∀ i, (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (f i)
      = ∑ j, (A i j : PowerSeries ℚ) * f j) :
    ∃ C : ℕ, ∀ (D : ℕ) (P : Fin m → Polynomial ℚ),
      (∀ i, (P i).degree < (D : WithBot ℕ)) →
      (∑ i, (P i : PowerSeries ℚ) * f i) ≠ 0 →
      (∑ i, (P i : PowerSeries ℚ) * f i).order ≤ (m * D + C : ℕ∞) := by
  classical
  obtain ⟨c, hL2⟩ := hL2
  obtain ⟨N, hN⟩ := Work.ZeroEst.fixed_deg_order_bound m f c
  refine ⟨m * m * Work.ZeroEst.dlt q A + N + m, ?_⟩
  intro D P hPdeg hRne
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact absurd hRne (by simp)
  have hDeg : Work.ZeroEst.DegLT P D := (Work.ZeroEst.DegLT_iff_degree P D).mpr hPdeg
  have hPne : P ≠ 0 := by
    intro h
    exact hRne (by simp [h])
  have hD1 : 1 ≤ D := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hPne
    have h := hPdeg j
    rw [Polynomial.degree_eq_natDegree hj] at h
    have hlt : (P j).natDegree < D := by exact_mod_cast h
    omega
  -- L1: the rank of the orbit
  obtain ⟨r, hr1, hrm, hind, hVr⟩ :=
    orbit_rank_gen q A P hPne (fun k => Work.ZeroEst.orbit q A P k) rfl (by
      intro k
      funext i
      rw [Work.ZeroEst.orbit_succ]
      rfl)
  -- `Λ`-stability of the span of the first `r` orbit vectors
  have hstab : ∀ k : Fin r, (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
      (q * Polynomial.derivative (Work.ZeroEst.orbit q A P (k : ℕ) j)
        + ∑ i, Work.ZeroEst.orbit q A P (k : ℕ) i * A i j)) ∈
      Submodule.span (RatFunc ℚ) (Set.range fun k : Fin r => fun j =>
        algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.ZeroEst.orbit q A P (k : ℕ) j)) := by
    intro k
    have hk : (k : ℕ) + 1 ≤ r := by have := k.isLt; omega
    have hstep : (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
        (q * Polynomial.derivative (Work.ZeroEst.orbit q A P (k : ℕ) j)
          + ∑ i, Work.ZeroEst.orbit q A P (k : ℕ) i * A i j))
        = fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
            (Work.ZeroEst.orbit q A P ((k : ℕ) + 1) j) := by
      funext j
      rw [show q * Polynomial.derivative (Work.ZeroEst.orbit q A P (k : ℕ) j)
            + ∑ i, Work.ZeroEst.orbit q A P (k : ℕ) i * A i j
          = Work.ZeroEst.orbit q A P ((k : ℕ) + 1) j from by
        rw [show Work.ZeroEst.orbit q A P ((k : ℕ) + 1)
              = Work.ZeroEst.Lam q A (Work.ZeroEst.orbit q A P (k : ℕ))
            from Work.ZeroEst.orbit_succ q A P (k : ℕ)]
        rfl]
    rw [hstep]
    rcases lt_or_eq_of_le hk with hlt | heq
    · exact Submodule.subset_span ⟨⟨(k : ℕ) + 1, hlt⟩, rfl⟩
    · rw [heq]
      exact hVr
  -- L2: a bounded-degree polynomial basis of the span
  obtain ⟨v, hvdeg, hvspan⟩ := hL2 r (fun k : Fin r => Work.ZeroEst.orbit q A P (k : ℕ))
    hind hstab
  -- some row of the basis is nonzero
  have hex : ∃ i : Fin r, v i ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ i : Fin r, v i = 0 := fun i => by
      by_contra h
      exact hcon ⟨i, h⟩
    have hbot : Submodule.span (RatFunc ℚ) (Set.range fun k : Fin r => fun j =>
        algebraMap (Polynomial ℚ) (RatFunc ℚ) (v k j)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro x ⟨k, rfl⟩
      show (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (v k j)) = 0
      rw [hcon' k]
      funext j
      simp
    have hmem : (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (P j)) ∈
        Submodule.span (RatFunc ℚ) (Set.range fun k : Fin r => fun j =>
          algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.ZeroEst.orbit q A P (k : ℕ) j)) :=
      Submodule.subset_span ⟨⟨0, hr1⟩, rfl⟩
    rw [← hvspan] at hmem
    rw [hbot] at hmem
    have hP0 : (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (P j)) ≠ 0 := by
      intro hh
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hPne
      exact hj (by simpa using congr_fun hh j)
    exact hP0 (by simpa using hmem)
  obtain ⟨i, hvi⟩ := hex
  -- the auxiliary combination `g = ⟨vᵢ, f⟩` is nonzero of bounded order
  have hg_ne : (∑ j, (v i j : PowerSeries ℚ) * f j) ≠ 0 := by
    intro h
    exact hvi (funext fun j => hpi (v i) h j)
  have hg_ord : (∑ j, (v i j : PowerSeries ℚ) * f j).order ≤ (N : ℕ∞) := by
    refine hN (v i) ?_ hg_ne
    intro j
    exact Polynomial.natDegree_le_iff_degree_le.mp (hvdeg i j)
  -- the column selection: an invertible `r × r` minor of the orbit rows
  obtain ⟨I, _hIinj, hIdet⟩ := exists_injective_minor
    (fun k : Fin r => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
      (Work.ZeroEst.orbit q A P (k : ℕ) j)) hind
  -- the Cramer identity
  have hid := cramer_identity v (fun k : Fin r => Work.ZeroEst.orbit q A P (k : ℕ))
    I hvspan hIdet f
  -- the objects of the order computation
  let d : Polynomial ℚ := (Matrix.of (fun k b : Fin r =>
    Work.ZeroEst.orbit q A P (k : ℕ) (I b))).det
  let Lm : Fin r → Polynomial ℚ := fun k => ((Matrix.of (fun a b : Fin r => v a (I b))) *
    (Matrix.of (fun k b : Fin r => Work.ZeroEst.orbit q A P (k : ℕ) (I b))).adjugate) i k
  let R : Fin r → PowerSeries ℚ := fun k =>
    ∑ j, (Work.ZeroEst.orbit q A P (k : ℕ) j : PowerSeries ℚ) * f j
  have hd_ne : d ≠ 0 := by
    intro h
    apply hIdet
    have h1 : (Matrix.of (fun k b : Fin r => algebraMap (Polynomial ℚ) (RatFunc ℚ)
        (Work.ZeroEst.orbit q A P (k : ℕ) (I b))))
        = (algebraMap (Polynomial ℚ) (RatFunc ℚ)).mapMatrix
            (Matrix.of (fun k b : Fin r => Work.ZeroEst.orbit q A P (k : ℕ) (I b))) := by
      ext a b; rfl
    rw [h1, ← RingHom.map_det]
    show algebraMap (Polynomial ℚ) (RatFunc ℚ) d = 0
    rw [h]
    simp
  have hid_inst : (d : PowerSeries ℚ) * (∑ j, (v i j : PowerSeries ℚ) * f j)
      = ∑ k, (Lm k : PowerSeries ℚ) * R k := hid i
  have hord : ∀ k : Fin r,
      (((R ⟨0, hr1⟩).order.toNat - ((k : ℕ) - ((⟨0, hr1⟩ : Fin r) : ℕ)) : ℕ) : ℕ∞) ≤ (R k).order := by
    intro k
    have hsub : ((k : ℕ) - ((⟨0, hr1⟩ : Fin r) : ℕ)) = (k : ℕ) := by simp
    rw [hsub]
    rw [show R k = ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[(k : ℕ)])
        (∑ i, (P i : PowerSeries ℚ) * f i)
      from Work.ZeroEst.case_det_orbit_dot m q A f hrel P (k : ℕ)]
    exact Work.ZeroEst.case_det_order_iter q (∑ i, (P i : PowerSeries ℚ) * f i) (k : ℕ)
  have hfin : (R ⟨0, hr1⟩).order.toNat ≤ (r - 1) + d.natDegree + N :=
    order_bound_cramer R (∑ j, (v i j : PowerSeries ℚ) * f j) d Lm N ⟨0, hr1⟩
      hd_ne hg_ne hg_ord hord hid_inst
  -- degree bound for `d`
  have hdegdet : d.natDegree ≤ r * (D + (m - 1) * Work.ZeroEst.dlt q A) := by
    refine Work.ZeroEst.case_det_detdeg _ _ ?_
    intro a b
    have h := (Work.ZeroEst.DegLT_iff_degree _ _).mp
      (Work.ZeroEst.orbit_DegLT q A P D hD1 hDeg (a : ℕ)) (I b)
    have hle : D + (a : ℕ) * Work.ZeroEst.dlt q A ≤ D + (m - 1) * Work.ZeroEst.dlt q A := by
      have ha : (a : ℕ) ≤ m - 1 := by have := a.isLt; omega
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ ha) D
    exact Polynomial.natDegree_le_iff_degree_le.mpr
      (le_of_lt (lt_of_lt_of_le h (by exact_mod_cast hle)))
  -- final arithmetic
  rw [← PowerSeries.coe_toNat_order hRne]
  refine ENat.natCast_le_natCast.mpr ?_
  refine le_trans hfin ?_
  have hrD : r * D ≤ m * D := Nat.mul_le_mul_right D hrm
  have hrδ : r * ((m - 1) * Work.ZeroEst.dlt q A) ≤ m * m * Work.ZeroEst.dlt q A := by
    calc r * ((m - 1) * Work.ZeroEst.dlt q A)
        = (r * (m - 1)) * Work.ZeroEst.dlt q A := (mul_assoc _ _ _).symm
      _ ≤ (m * m) * Work.ZeroEst.dlt q A :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul hrm (Nat.sub_le m 1))
      _ = m * m * Work.ZeroEst.dlt q A := rfl
  have hd2 : r * (D + (m - 1) * Work.ZeroEst.dlt q A)
      = r * D + r * ((m - 1) * Work.ZeroEst.dlt q A) := Nat.mul_add _ _ _
  have hdegb : d.natDegree ≤ r * D + r * ((m - 1) * Work.ZeroEst.dlt q A) := by
    rw [← hd2]; exact hdegdet
  calc (r - 1) + d.natDegree + N
      ≤ (r - 1) + (r * D + r * ((m - 1) * Work.ZeroEst.dlt q A)) + N := by omega
    _ ≤ (r - 1) + (m * D + m * m * Work.ZeroEst.dlt q A) + N := by
        have := add_le_add hrD hrδ; omega
    _ ≤ m * D + (m * m * Work.ZeroEst.dlt q A + N + m) := by omega


end Work.ZeroEst2
