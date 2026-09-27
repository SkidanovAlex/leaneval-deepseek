import Mathlib
import Submission.Work.Noncompact.ProperLine.rayAssembly

/-!
# The assembly of the proper ray from its pieces
-/

open Set Filter Topology
open scoped Manifold ContDiff

namespace Work.Noncompact.ProperLine

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M]

/-- **Smoothness at a junction.** -/
theorem contMDiffAt_junction {A B : ℝ → M} {τ : ℝ} {p : M}
    (hA : ContMDiff 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContMDiff 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hAp : ∀ t, τ ≤ t → A t = p) (hBp : ∀ t, t ≤ τ → B t = p) :
    ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t => if t ≤ τ then A t else B t) τ := by
  have hAτ : A τ = p := hAp τ le_rfl
  have hBτ : B τ = p := hBp τ le_rfl
  have hsrc : (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).source ∈ 𝓝 p :=
    extChartAt_source_mem_nhds p
  have hAev : ∀ᶠ t in 𝓝 τ, A t ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).source := by
    have h2 : (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).source ∈ 𝓝 (A τ) := by
      rw [hAτ]; exact hsrc
    exact hA.continuous.continuousAt.eventually h2
  have hBev : ∀ᶠ t in 𝓝 τ, B t ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).source := by
    have h2 : (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).source ∈ 𝓝 (B τ) := by
      rw [hBτ]; exact hsrc
    exact hB.continuous.continuousAt.eventually h2
  have h1 : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p (A t)) τ := by
    have hg : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (↑(extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p)) (A τ) := by
      rw [hAτ]
      exact contMDiffAt_extChartAt
    exact hg.comp τ hA.contMDiffAt
  have h2 : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p (B t)) τ := by
    have hg : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (↑(extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p)) (B τ) := by
      rw [hBτ]
      exact contMDiffAt_extChartAt
    exact hg.comp τ hB.contMDiffAt
  set Φ : ℝ → EuclideanSpace ℝ (Fin n) :=
    fun t => extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p (A t)
      + extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p (B t)
      - extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p p with hΦ
  have hΦsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ τ := by
    rw [hΦ]
    exact (h1.contDiffAt.add h2.contDiffAt).sub contDiffAt_const
  have hsymm : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t => (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).symm (Φ t)) τ := by
    have hg : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (↑(extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).symm) (Φ τ) := by
      have hmem : Φ τ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).target := by
        have hΦτ : Φ τ = extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p p := by
          rw [hΦ]; simp only; rw [hAτ, hBτ]; abel
        rw [hΦτ]
        exact mem_extChartAt_target p
      have hOn := contMDiffOn_extChartAt_symm
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) p
      exact hOn.contMDiffAt ((isOpen_extChartAt_target p).mem_nhds hmem)
    exact hg.comp τ hΦsm.contMDiffAt
  refine hsymm.congr_of_eventuallyEq ?_
  filter_upwards [hAev, hBev] with t hAs hBs
  by_cases h : t ≤ τ
  · have hBt : B t = p := hBp t h
    have hthis : Φ t = extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p (A t) := by
      rw [hΦ]; simp only; rw [hBt]; abel
    rw [if_pos h, hthis]
    exact ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).left_inv hAs).symm
  · have hAt : A t = p := hAp t (le_of_lt (not_le.mp h))
    have hthis : Φ t = extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p (B t) := by
      rw [hΦ]; simp only; rw [hAt]; abel
    rw [if_neg h, hthis]
    exact ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p).left_inv hBs).symm

end Work.Noncompact.ProperLine

namespace Work.Noncompact.ProperLine

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [SecondCountableTopology M]

/-- **The assembled ray.** -/
theorem rayAssembly_of_pieces {C : Set M} {b : M} {P : ℕ → ℝ → M}
    (hPsm : ∀ i, ContMDiff 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (P i))
    (hP0 : ∀ i u, u ≤ 0 → P i u = P i 0)
    (hP1 : ∀ i u, 1 ≤ u → P i u = P i 1)
    (hPmem : ∀ i, P i '' Set.Icc (0:ℝ) 1 ⊆ C)
    (hPinj : ∀ i, Set.InjOn (P i) (Set.Icc (0:ℝ) 1))
    (hP00 : P 0 0 = b)
    (hjun : ∀ i, P (i + 1) 0 = P i 1)
    (hsep : ∀ i j, i < j → P i '' Set.Icc (0:ℝ) 1 ∩ P j '' Set.Icc (0:ℝ) 1 ⊆ {P i 1})
    (hnotb : ∀ i, 1 ≤ i → ∀ u ∈ Set.Icc (0:ℝ) 1, P i u ≠ b)
    (hdeep : ∀ K' : Set M, IsCompact K' → ∃ I, ∀ i, I ≤ i →
      P i '' Set.Icc (0:ℝ) 1 ∩ K' = ∅) :
    ∃ r : ℝ → M, (∀ t, t ≤ 0 → r t = b) ∧
      ContMDiff 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞) r ∧
      Set.InjOn r (Set.Ici 0) ∧
      IsProperMap (fun t : Set.Ici (0 : ℝ) => r t) ∧ Set.range r ⊆ C := by
  set r : ℝ → M := fun t => if t ≤ 0 then b else P (Nat.floor t) (t - Nat.floor t) with hr
  have hrpos : ∀ {s : ℝ}, 0 < s → r s = P (Nat.floor s) (s - Nat.floor s) := by
    intro s hs; rw [hr]; exact if_neg (not_le.mpr hs)
  have hrnp : ∀ {s : ℝ}, s ≤ 0 → r s = b := by
    intro s hs; rw [hr]; exact if_pos hs
  have hstep : ∀ {s : ℝ}, 0 < s → s - (Nat.floor s : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    intro s hs
    exact ⟨by linarith [Nat.floor_le hs.le], by linarith [Nat.lt_floor_add_one s]⟩
  -- membership
  have hmem' : ∀ {s : ℝ}, 0 < s → r s ∈ C := by
    intro s hs
    rw [hrpos hs]
    exact hPmem _ ⟨_, hstep hs, rfl⟩
  have hmem : ∀ s, r s ∈ C := by
    intro s
    by_cases h : s ≤ 0
    · rw [hrnp h, ← hP00]
      exact hPmem 0 ⟨0, Set.left_mem_Icc.mpr zero_le_one, rfl⟩
    · exact hmem' (not_le.mp h)
  -- smoothness
  have hsm : ContMDiff 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞) r := by
    intro t
    rcases lt_trichotomy t 0 with ht | ht | ht
    · refine (contMDiffAt_const (c := b)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
      exact hrnp (le_of_lt hs)
    · subst ht
      have hev : r =ᶠ[𝓝 (0:ℝ)] (fun s => if s ≤ 0 then b else P 0 s) := by
        filter_upwards [Ioo_mem_nhds (show (-1:ℝ) < 0 by norm_num)
          (show (0:ℝ) < 1 by norm_num)] with s hs
        rcases lt_trichotomy s 0 with h | h | h
        · rw [hrnp (le_of_lt h), if_pos (le_of_lt h)]
        · subst h; rw [hrnp le_rfl, if_pos le_rfl]
        · rw [hrpos h, if_neg (not_le.mpr h)]
          have hfl : Nat.floor s = 0 :=
            (Nat.floor_eq_iff h.le).mpr ⟨by simpa using h.le, by simpa using hs.2⟩
          rw [hfl]
          norm_num
      refine (contMDiffAt_junction (A := fun _ : ℝ => b) (B := P 0) (τ := 0) (p := b)
        contMDiff_const (hPsm 0) (fun u _ => rfl)
        (fun u hu => by rw [hP0 0 u hu, hP00])).congr_of_eventuallyEq hev
    · rcases eq_or_ne t ((Nat.floor t : ℕ) : ℝ) with heq | hne
      · -- junction at the integer `i = ⌊t⌋ ≥ 1`
        set i : ℕ := Nat.floor t with hi
        have hti : (i : ℝ) = t := by rw [hi]; exact heq.symm
        have hi1 : 1 ≤ i := by
          rcases Nat.eq_zero_or_pos i with h | h
          · exfalso; rw [h] at hti; simp only [Nat.cast_zero] at hti; linarith
          · exact h
        have hjun' : P i 0 = P (i - 1) 1 := by
          have hh := hjun (i - 1); rwa [Nat.sub_add_cancel hi1] at hh
        have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
          rw [Nat.cast_sub hi1]; norm_num
        have hglue : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun s => if s ≤ (i:ℝ) then P (i - 1) (s - ((i - 1 : ℕ) : ℝ))
              else P i (s - (i:ℝ))) t := by
          rw [← hti]
          exact contMDiffAt_junction
            (A := fun s => P (i - 1) (s - ((i - 1 : ℕ) : ℝ)))
            (B := fun s => P i (s - (i:ℝ))) (τ := (i:ℝ)) (p := P (i - 1) 1)
            ((hPsm (i - 1)).comp (contMDiff_id.sub contMDiff_const))
            ((hPsm i).comp (contMDiff_id.sub contMDiff_const))
            (fun s hs => by
              rw [hP1 (i - 1) (s - ((i - 1 : ℕ) : ℝ)) (by rw [hcast]; linarith)])
            (fun s hs => by rw [hP0 i (s - (i:ℝ)) (by linarith [hs]), hjun'])
        have hev : r =ᶠ[𝓝 t] (fun s => if s ≤ (i:ℝ) then P (i - 1) (s - ((i - 1 : ℕ) : ℝ))
              else P i (s - (i:ℝ))) := by
          filter_upwards [Ioo_mem_nhds (by linarith [hti] : (i:ℝ) - 1 < t)
            (by linarith [hti] : t < (i:ℝ) + 1)] with s hs
          rw [Set.mem_Ioo] at hs
          have hs0 : 0 < s := by
            have : (0:ℝ) ≤ (i:ℝ) - 1 := by rw [← hcast]; positivity
            linarith [hs.1]
          rcases lt_trichotomy s (i:ℝ) with h | h | h
          · have hfl : Nat.floor s = i - 1 :=
              (Nat.floor_eq_iff hs0.le).mpr ⟨by rw [hcast]; linarith [hs.1], by rw [hcast]; linarith [h]⟩
            rw [hrpos hs0, if_pos h.le, hfl]
          · subst h
            rw [hrpos hs0, if_pos le_rfl, Nat.floor_natCast, sub_self, hjun']
            congr 1; rw [hcast]; ring
          · have hfl : Nat.floor s = i :=
              (Nat.floor_eq_iff hs0.le).mpr ⟨le_of_lt h, hs.2⟩
            rw [hrpos hs0, if_neg (not_le.mpr h), hfl]
        exact hglue.congr_of_eventuallyEq hev
      · -- interior of a unit interval
        set i : ℕ := Nat.floor t with hi
        have hlt : (i : ℝ) < t := lt_of_le_of_ne (Nat.floor_le ht.le) (by
          intro hc; exact hne (by rw [hi]; exact hc.symm))
        have hlt2 : t < (i : ℝ) + 1 := Nat.lt_floor_add_one t
        have hcomp : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun s : ℝ => P i (s - (i:ℝ))) t :=
          ((hPsm i).comp (contMDiff_id.sub contMDiff_const)).contMDiffAt
        refine hcomp.congr_of_eventuallyEq ?_
        filter_upwards [Ioo_mem_nhds hlt hlt2] with s hs
        have hs0 : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg i) hs.1
        have hfl : Nat.floor s = i := (Nat.floor_eq_iff hs0.le).mpr ⟨le_of_lt hs.1, hs.2⟩
        rw [hrpos hs0, hfl]
  refine ⟨r, fun t ht => hrnp ht, hsm, ?_, ?_, ?_⟩
  · -- injectivity
    intro s hs t ht hst
    have hs0 : 0 ≤ s := hs
    have ht0 : 0 ≤ t := ht
    rcases eq_or_lt_of_le hs0 with h | hspos
    · subst h
      rw [hrnp le_rfl] at hst
      rcases eq_or_lt_of_le ht0 with h | htpos
      · exact h
      · exfalso
        rw [hrpos htpos] at hst
        have hu := hstep htpos
        rcases Nat.eq_zero_or_pos (Nat.floor t) with hc | hc
        · have hst' : b = P 0 t := by rw [hc] at hst; simpa using hst
          have hu' : t ∈ Set.Icc (0:ℝ) 1 := by
            have htfl : t - (Nat.floor t : ℝ) = t := by rw [hc]; norm_num
            rwa [htfl] at hu
          have hz : (0:ℝ) = t :=
            hPinj 0 (Set.left_mem_Icc.mpr zero_le_one) hu' (by rw [hP00]; exact hst')
          linarith
        · exact absurd (hst.symm) (hnotb _ hc _ hu)
    · rcases eq_or_lt_of_le ht0 with h | htpos
      · subst h
        rw [hrnp le_rfl] at hst
        exfalso
        rw [hrpos hspos] at hst
        have hu := hstep hspos
        rcases Nat.eq_zero_or_pos (Nat.floor s) with hc | hc
        · have hst' : P 0 s = b := by rw [hc] at hst; simpa using hst
          have hu' : s ∈ Set.Icc (0:ℝ) 1 := by
            have hsfl : s - (Nat.floor s : ℝ) = s := by rw [hc]; norm_num
            rwa [hsfl] at hu
          have hz : (0:ℝ) = s :=
            hPinj 0 (Set.left_mem_Icc.mpr zero_le_one) hu' (by rw [hP00]; exact hst'.symm)
          linarith
        · exact absurd hst (hnotb _ hc _ hu)
      · rw [hrpos hspos, hrpos htpos] at hst
        have hsu := hstep hspos
        have htu := hstep htpos
        rcases lt_trichotomy (Nat.floor s) (Nat.floor t) with hlt | heq | hgt
        · have hmem : P (Nat.floor s) (s - (Nat.floor s : ℝ)) ∈
              P (Nat.floor s) '' Set.Icc (0:ℝ) 1 ∩ P (Nat.floor t) '' Set.Icc (0:ℝ) 1 :=
            ⟨⟨_, hsu, rfl⟩, ⟨_, htu, hst.symm⟩⟩
          have h1 := hsep _ _ hlt hmem
          rw [Set.mem_singleton_iff] at h1
          have h2 : s - (Nat.floor s : ℝ) = 1 :=
            hPinj _ hsu (Set.right_mem_Icc.mpr zero_le_one) h1
          linarith [Nat.lt_floor_add_one s]
        · rw [← heq] at hst htu
          have h3 := hPinj _ hsu htu hst
          linarith [Nat.floor_le hspos.le]
        · have hmem : P (Nat.floor t) (t - (Nat.floor t : ℝ)) ∈
              P (Nat.floor t) '' Set.Icc (0:ℝ) 1 ∩ P (Nat.floor s) '' Set.Icc (0:ℝ) 1 :=
            ⟨⟨_, htu, rfl⟩, ⟨_, hsu, hst⟩⟩
          have h1 := hsep _ _ hgt hmem
          rw [Set.mem_singleton_iff] at h1
          have h2 : t - (Nat.floor t : ℝ) = 1 :=
            hPinj _ htu (Set.right_mem_Icc.mpr zero_le_one) h1
          linarith [Nat.lt_floor_add_one t]
  · -- properness
    refine (isProperMap_iff_isCompact_preimage).mpr ⟨hsm.continuous.comp continuous_subtype_val, ?_⟩
    intro K' hK'
    obtain ⟨I, hI⟩ := hdeep K' hK'
    have hcomp : IsCompact {p : Set.Ici (0:ℝ) | (p:ℝ) ≤ (I:ℝ) + 1} := by
      have h : IsCompact ((Subtype.val : Set.Ici (0:ℝ) → ℝ) ⁻¹' Set.Icc (0:ℝ) ((I:ℝ)+1)) :=
        isClosed_Ici.isClosedEmbedding_subtypeVal.isCompact_preimage isCompact_Icc
      have hset : (Subtype.val ⁻¹' Set.Icc (0:ℝ) ((I:ℝ)+1) : Set (Set.Ici (0:ℝ)))
          = {p : Set.Ici (0:ℝ) | (p:ℝ) ≤ (I:ℝ) + 1} := by
        ext p
        simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq]
        exact ⟨fun h => h.2, fun h => ⟨p.2, h⟩⟩
      rwa [hset] at h
    refine IsCompact.of_isClosed_subset hcomp ?_ ?_
    · exact hK'.isClosed.preimage (hsm.continuous.comp continuous_subtype_val)
    · rintro p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      by_contra hcon
      push_neg at hcon
      have hp0 : 0 < (p:ℝ) := lt_of_le_of_lt (by positivity) hcon
      rw [Set.mem_preimage, hrpos hp0] at hp
      have hle : I ≤ Nat.floor (p:ℝ) :=
        Nat.le_floor (a := (p:ℝ)) (by linarith)
      have hmemK : P (Nat.floor (p:ℝ)) ((p:ℝ) - (Nat.floor (p:ℝ) : ℝ)) ∈ K' := hp
      have h1 := hI _ hle
      exact Set.eq_empty_iff_forall_notMem.mp h1 _ ⟨⟨_, hstep hp0, rfl⟩, hmemK⟩
  · -- range
    rintro y ⟨t, rfl⟩
    exact hmem t

end Work.Noncompact.ProperLine
