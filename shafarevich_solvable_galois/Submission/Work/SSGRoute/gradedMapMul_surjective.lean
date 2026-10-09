import Mathlib
import Submission.Work.CohomologicalShrinking.All
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.ProP.lowerCentralSeries_le_pCentralSeries
import Submission.Work.SSGRoute.pSeries_inter_centralSeries_pow
import Submission.Work.SSGRoute.UnivPort
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Surjectivity of the graded map `E(m,τ) → E(n,τ)`

`Work.SSGRoute.gradedMapMul_surjective`: for a surjective `G`-operator homomorphism
`Φ : F(m) ⇢ F(n)` of free `G`-operator groups and all `i j : ℕ`, the induced map
`gradedMapMul p Φ.toHom Φ.surjective i j` on the graded pieces of the refined
`p`-central filtration is surjective.

The proof is a port to *arbitrary* `p` (Schmidt–Wingberg's Lemma 4(ii) normally assumes
`p` prime) of the `⊆` half of Lemma 4(ii) for free groups, combined with the observation that
`R_Q = ψ(R_P) · D_Q`; see the lemmas below.
-/

attribute [local instance] Classical.decEq

namespace Work.SSGRoute

universe u

open Work.CohomologicalShrinking

/-! ## The case `p = 0`: the `p`-central series is the lower central series -/

/-- `powSubgroup 0 H = ⊥`. -/
theorem powSubgroup_zero {P : Type*} [Group P] (H : Subgroup P) :
    Work.Shrinking.powSubgroup 0 H = ⊥ := by
  rw [Work.Shrinking.powSubgroup]
  refine le_antisymm ?_ bot_le
  rw [Subgroup.closure_le]
  rintro x ⟨y, hy, rfl⟩
  simp

/-- For `p = 0` the descending `p`-central series is the descending central series. -/
theorem pCentralSeries_zero_eq_lcs (P : Type*) [Group P] (n : ℕ) :
    Work.Shrinking.pCentralSeries 0 P n = (⊤ : Subgroup P).lowerCentralSeries n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Shrinking.pCentralSeries_succ, Work.Shrinking.pCentralStep, ih,
        powSubgroup_zero, bot_sup_eq, Subgroup.lowerCentralSeries_succ]

/-- For `p = 0` a refined term is a term of the lower central series. -/
theorem refinedTerm_zero_eq (P : Type*) [Group P] (i j : ℕ) :
    refinedTerm 0 P i j
      = (⊤ : Subgroup P).lowerCentralSeries (min (max (i - 1) (j - 1)) i) := by
  rw [refinedTerm]
  have h1 : Work.CohomologicalShrinking.pSeries 0 P i
      = (⊤ : Subgroup P).lowerCentralSeries (i - 1) :=
    pCentralSeries_zero_eq_lcs P (i - 1)
  have h2 : Work.CohomologicalShrinking.pSeries 0 P (i + 1)
      = (⊤ : Subgroup P).lowerCentralSeries i :=
    pCentralSeries_zero_eq_lcs P i
  have h3 : centralSeries P j = (⊤ : Subgroup P).lowerCentralSeries (j - 1) := rfl
  rw [h1, h2, h3]
  have hanti := Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup P)
  have hinf : (⊤ : Subgroup P).lowerCentralSeries (i - 1)
        ⊓ (⊤ : Subgroup P).lowerCentralSeries (j - 1)
      = (⊤ : Subgroup P).lowerCentralSeries (max (i - 1) (j - 1)) := by
    refine le_antisymm ?_ (le_inf (hanti (le_max_left _ _)) (hanti (le_max_right _ _)))
    rcases le_total (i - 1) (j - 1) with h | h
    · rw [max_eq_right h]; exact inf_le_right
    · rw [max_eq_left h]; exact inf_le_left
  rw [hinf]
  have hsup : (⊤ : Subgroup P).lowerCentralSeries (max (i - 1) (j - 1))
        ⊔ (⊤ : Subgroup P).lowerCentralSeries i
      = (⊤ : Subgroup P).lowerCentralSeries (min (max (i - 1) (j - 1)) i) := by
    refine le_antisymm (sup_le (hanti (min_le_left _ _)) (hanti (min_le_right _ _))) ?_
    rcases le_total (max (i - 1) (j - 1)) i with h | h
    · rw [min_eq_left h]; exact le_sup_left
    · rw [min_eq_right h]; exact le_sup_right
  rw [hsup]

/-- The lower central series is compatible with a surjective homomorphism. -/
theorem map_lowerCentralSeries_eq {P Q : Type*} [Group P] [Group Q] (ψ : P →* Q)
    (hψ : Function.Surjective ψ) (k : ℕ) :
    ((⊤ : Subgroup P).lowerCentralSeries k).map ψ = (⊤ : Subgroup Q).lowerCentralSeries k := by
  have h := map_centralSeries_eq_of_surjective ψ hψ (k + 1)
  simpa [centralSeries] using h

/-- For `j = 0` a refined term is just the corresponding `p`-central series term. -/
theorem refinedTerm_zero_snd (p : ℕ) (P : Type*) [Group P] (i : ℕ) :
    Work.CohomologicalShrinking.refinedTerm p P i 0 = Work.CohomologicalShrinking.pSeries p P i := by
  rw [Work.CohomologicalShrinking.refinedTerm, Work.CohomologicalShrinking.centralSeries_zero,
    inf_top_eq, sup_eq_left]
  exact Work.CohomologicalShrinking.pSeries_antitone p P (Nat.le_succ i)

/-! ## Iterated powers of a lower central term -/

/-- `(γ_j)^{p^t} ≤ P_{j+t}`. -/
theorem powSubgroup_lcs_le_pCentralSeries (p : ℕ) {P : Type*} [Group P] (j t : ℕ) (hj : 1 ≤ j) :
    Work.Shrinking.powSubgroup (p ^ t) ((⊤ : Subgroup P).lowerCentralSeries (j - 1))
      ≤ Work.Shrinking.pCentralSeries p P (j + t - 1) := by
  rw [Work.Shrinking.powSubgroup, Subgroup.closure_le]
  rintro x ⟨y, hy, rfl⟩
  have key : ∀ s : ℕ,
      y ^ (p ^ s) ∈ Work.Shrinking.pCentralSeries p P (j - 1 + s) := by
    intro s
    induction s with
    | zero =>
        simpa using Work.ProP.lowerCentralSeries_le_pCentralSeries p P (j - 1) hy
    | succ s ih =>
        have h1 : y ^ p ^ (s + 1) = (y ^ p ^ s) ^ p := by rw [pow_succ, pow_mul]
        rw [h1, show j - 1 + (s + 1) = (j - 1 + s) + 1 from by omega]
        exact Work.Shrinking.pow_mem_pCentralSeries_succ p P ih
  have := key t
  rwa [show j - 1 + t = j + t - 1 from by omega] at this

/-- `p`-th power subgroups commute with a surjective homomorphism (one inclusion). -/
theorem powSubgroup_map_le {P Q : Type*} [Group P] [Group Q] (ψ : P →* Q) (n : ℕ)
    (H : Subgroup P) :
    Work.Shrinking.powSubgroup n (H.map ψ) ≤ (Work.Shrinking.powSubgroup n H).map ψ := by
  rw [Work.Shrinking.powSubgroup, Subgroup.closure_le]
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  show ψ z ^ n ∈ (Work.Shrinking.powSubgroup n H).map ψ
  rw [← map_pow]
  exact Subgroup.mem_map_of_mem ψ (Subgroup.subset_closure ⟨z, hz, rfl⟩)

/-! ## Lemma 4(ii) for arbitrary `p` -/

/-- `p^{i-j}`-divisibility of the Magnus leading term on `P_i ∩ γ_j`, for `0 < p`. -/
theorem magLT_pSeries_divisible_of_pos (p : ℕ) (hp : 0 < p) (X : Type u) (i j : ℕ) (hj : 1 ≤ j)
    (hji : j ≤ i) {x : FreeGroup X}
    (hxP : x ∈ Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1))
    (hxγ : x ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    ∃ a ∈ Work.SSGRoute.prop5.filq X (j + 1) j,
      Work.SSGRoute.prop5.magLT X j x = ((p : ℤ) ^ (i - j)) • a := by
  have hje : j + (i - j) = i := by omega
  have hA : ((Work.SSGRoute.prop5.magnus X (j + 1) x :
      (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1))ˣ) :
      Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1)) - 1
      ∈ Work.SSGRoute.prop5.wtqLT p X (j + 1) i := by
    have h := Work.SSGRoute.prop5.mag_mem_wtqLT p X (j + 1) (i - 1) hxP
    rwa [show i - 1 + 1 = i from by omega] at h
  obtain ⟨a0, ha0, ha0eq⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1)))
    Ideal.Quotient.mk_surjective).1 hA
  have hB : Work.SSGRoute.prop5.magLT X j x ∈ Work.SSGRoute.prop5.filq X (j + 1) j :=
    Work.SSGRoute.prop5.magLT_mem_filq X j hj hxγ
  have ha0f : a0 ∈ Work.SSGRoute.prop5.filz X j := by
    obtain ⟨c, hc, hceq⟩ := Work.SSGRoute.prop5.mem_filq_iff.1 hB
    have hker : a0 - c ∈ Work.SSGRoute.prop5.fil X (j + 1) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub,
        show (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1))) a0
            = Work.SSGRoute.prop5.magLT X j x from ha0eq, hceq, sub_self]
    have h2 : c + (a0 - c) ∈ Work.SSGRoute.prop5.filz X j :=
      Submodule.add_mem _ hc
        (Work.SSGRoute.filz_antitone_local_magLT X (by omega : j ≤ j + 1)
          (Work.SSGRoute.fil_le_filz_local_magLT X (j + 1) hker))
    rwa [add_sub_cancel] at h2
  have ha0' : a0 ∈ Work.SSGRoute.prop5.wtz p X (j + (i - j)) := by rw [hje]; exact ha0
  obtain ⟨b, hb, hbf⟩ := Work.SSGRoute.Up.wtz_filz_exists_pow_u p j (i - j) hp ha0' ha0f
  refine ⟨Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1)) b, ?_, ?_⟩
  · exact Ideal.mem_map_of_mem _ (Work.SSGRoute.prop5.filz_le_fil X j hb)
  · have h3 : (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1))) a0
        = (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1)))
            (((p : ℤ) ^ (i - j)) • b) := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hbf
    change ((Work.SSGRoute.prop5.magnus X (j + 1) x :
        (Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1))ˣ) :
        Work.SSGRoute.prop5.FreeAssoc X ⧸ Work.SSGRoute.prop5.fil X (j + 1)) - 1
      = ((p : ℤ) ^ (i - j)) • (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X (j + 1)) b)
    rw [← ha0eq, h3, map_zsmul]

/-- **Lemma 4(ii) (the `⊆` direction) for arbitrary `0 < p`.** For a free group `F`,
`F_i ∩ γ_j ≤ ⟨γ_j^{p^{i-j}}⟩ · γ_{j+1}`. -/
theorem pSeries_interCentral_pow_of_pos (p : ℕ) (hp : 0 < p) (X : Type u) (i j : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) :
    Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) ⊓
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)
      ≤ Work.Shrinking.powSubgroup (p ^ (i - j))
          ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
        ⊔ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
  classical
  obtain ⟨instLO, -⟩ := exists_wellFoundedLT X
  letI := instLO
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxP, hxγ⟩ := hx
  have hn : 0 < p ^ (i - j) := pow_pos hp _
  obtain ⟨a, ha, haeq⟩ := magLT_pSeries_divisible_of_pos p hp X i j hj hji hxP hxγ
  obtain ⟨w, hw, hweq⟩ :=
    Work.SSGRoute.Up.purity_aux j hj (p ^ (i - j)) hn hxγ ha (by
      rw [haeq, Nat.cast_pow])
  set z : FreeGroup X := x * (w ^ (p ^ (i - j)))⁻¹ with hz
  have hzγ : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
    Subgroup.mul_mem _ hxγ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hw _))
  have hwinv : (w ^ (p ^ (i - j)))⁻¹ ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ hw _)
  have hxn : Work.SSGRoute.prop5.magLT X j x = ((p ^ (i - j) : ℕ) : ℤ) • a := by
    rw [haeq, Nat.cast_pow]
  have hwn : Work.SSGRoute.prop5.magLT X j (w ^ (p ^ (i - j))) = ((p ^ (i - j) : ℕ) : ℤ) • a := by
    rw [Work.SSGRoute.prop5.magLT_pow X j hj (p ^ (i - j)) hw, hweq, zsmul_eq_mul]
  have hzlt : Work.SSGRoute.prop5.magLT X j z = 0 := by
    rw [hz, Work.SSGRoute.prop5.magLT_mul X j hj hxγ hwinv,
      Work.SSGRoute.prop5.magLT_inv X j hj (Subgroup.pow_mem _ hw _), hwn, hxn]
    abel
  have hzmem : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
    have h := Work.SSGRoute.UpCore.magnusCore_aux X j hj z
      (by simpa [Work.SSGRoute.UpCore.Gam, Work.SSGRoute.prop5.graded.Gam] using hzγ)
      (by simpa [Work.SSGRoute.prop5.magLT, Work.SSGRoute.prop5.magLead] using hzlt)
    simpa [Work.SSGRoute.UpCore.Gam, Work.SSGRoute.prop5.graded.Gam] using h
  have hdecomp : x = z * w ^ (p ^ (i - j)) := by rw [hz]; group
  rw [hdecomp]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hzmem)
    (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨w, hw, rfl⟩))


/-! ## The main inclusion `R_Q ≤ ψ(R_P) ⊔ D_Q` -/

/-- For `p = 0` the refined term is a lower central series term and `ψ` commutes with those. -/
theorem refinedTerm_zero_le_map {P X : Type*} [Group P] (ψ : P →* FreeGroup X)
    (hψ : Function.Surjective ψ) (i j : ℕ) :
    refinedTerm 0 (FreeGroup X) i j ≤ (refinedTerm 0 P i j).map ψ := by
  rw [refinedTerm_zero_eq (FreeGroup X), refinedTerm_zero_eq P,
      map_lowerCentralSeries_eq ψ hψ (min (max (i - 1) (j - 1)) i)]

/-- **The main inclusion.** For a surjective homomorphism onto the free group `FreeGroup X`, every
refined term of the target is contained in the image of the corresponding refined term of the
source together with the next refined term of the target. -/
theorem refinedTerm_le_map_sup_aux {P X : Type*} [Group P] (p : ℕ)
    (ψ : P →* FreeGroup X) (hψ : Function.Surjective ψ) (i j : ℕ) :
    refinedTerm p (FreeGroup X) i j
      ≤ Subgroup.map ψ (refinedTerm p P i j)
        ⊔ refinedTerm p (FreeGroup X) (tauSucc i j).1 (tauSucc i j).2 := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · rw [hp0]
    exact le_trans (refinedTerm_zero_le_map ψ hψ i j) le_sup_left
  · show (Work.CohomologicalShrinking.pSeries p (FreeGroup X) i
            ⊓ Work.CohomologicalShrinking.centralSeries (FreeGroup X) j)
          ⊔ Work.CohomologicalShrinking.pSeries p (FreeGroup X) (i + 1)
        ≤ Subgroup.map ψ (refinedTerm p P i j)
          ⊔ refinedTerm p (FreeGroup X) (tauSucc i j).1 (tauSucc i j).2
    refine sup_le ?_ ?_
    · -- the piece `Q_i ∩ γ_j`
      intro y hy
      rw [Subgroup.mem_inf] at hy
      obtain ⟨hyQ, hyγ⟩ := hy
      rcases Nat.eq_zero_or_pos j with hj0 | hj
      · -- `j = 0`
        rw [hj0, refinedTerm_zero_snd]
        have h : y ∈ Work.Shrinking.pCentralSeries p (FreeGroup X) (i - 1) := hyQ
        rw [← Work.Shrinking.map_pCentralSeries_surjective p ψ hψ (i - 1)] at h
        exact Subgroup.mem_sup_left h
      · rcases Nat.eq_zero_or_pos i with hi0 | hi
        · -- `i = 0`
          have htop : Work.CohomologicalShrinking.refinedTerm p P 0 j = ⊤ := by
            rw [Work.CohomologicalShrinking.refinedTerm]; simp
          rw [hi0, htop, Subgroup.map_top_of_surjective ψ hψ]
          exact Subgroup.mem_sup_left (Subgroup.mem_top y)
        · rcases lt_or_ge i j with hij | hji
          · -- `i < j`
            have hyγ' : y ∈ ((⊤ : Subgroup P).lowerCentralSeries (j - 1)).map ψ := by
              rw [map_lowerCentralSeries_eq ψ hψ (j - 1)]
              exact hyγ
            have hle : (⊤ : Subgroup P).lowerCentralSeries (j - 1)
                ≤ Work.CohomologicalShrinking.pSeries p P (i + 1) :=
              le_trans (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup P) (by omega))
                (Work.ProP.lowerCentralSeries_le_pCentralSeries p P i)
            refine Subgroup.mem_sup_left (Subgroup.map_mono ?_
              (Subgroup.map_mono hle hyγ'))
            exact le_sup_right
          · -- `1 ≤ j ≤ i` : Lemma 4(ii)
            have hKEY := pSeries_interCentral_pow_of_pos p hp X i j hj hji
            have hy' : y ∈ Work.Shrinking.powSubgroup (p ^ (i - j))
                  ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
                ⊔ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j :=
              hKEY (Subgroup.mem_inf.mpr ⟨hyQ, hyγ⟩)
            haveI : ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j).Normal :=
              Subgroup.lowerCentralSeries_normal (⊤ : Subgroup (FreeGroup X)) j
            obtain ⟨w, hw, g, hg, hwg⟩ := Subgroup.mem_sup_of_normal_right.mp hy'
            rw [← hwg]
            refine Subgroup.mul_mem _ ?_ ?_
            · -- `w ∈ ψ(R_P)`
              refine Subgroup.mem_sup_left ?_
              have h1 : w ∈ Work.Shrinking.powSubgroup (p ^ (i - j))
                  (((⊤ : Subgroup P).lowerCentralSeries (j - 1)).map ψ) := by
                rw [← map_lowerCentralSeries_eq ψ hψ (j - 1)] at hw
                exact hw
              refine Subgroup.map_mono ?_ (powSubgroup_map_le ψ (p ^ (i - j))
                ((⊤ : Subgroup P).lowerCentralSeries (j - 1)) h1)
              have hA : Work.Shrinking.powSubgroup (p ^ (i - j))
                    ((⊤ : Subgroup P).lowerCentralSeries (j - 1))
                  ≤ Work.Shrinking.pCentralSeries p P (i - 1) := by
                refine le_trans (powSubgroup_lcs_le_pCentralSeries p j (i - j) hj) ?_
                rw [show j + (i - j) - 1 = i - 1 from by omega]
              have hB : Work.Shrinking.powSubgroup (p ^ (i - j))
                    ((⊤ : Subgroup P).lowerCentralSeries (j - 1))
                  ≤ Work.CohomologicalShrinking.centralSeries P j :=
                Work.Shrinking.powSubgroup_le _ _
              exact le_trans (le_inf hA hB) le_sup_left
            · -- `g ∈ D_Q`
              have hwQ : w ∈ Work.CohomologicalShrinking.pSeries p (FreeGroup X) i := by
                have h := powSubgroup_lcs_le_pCentralSeries p j (i - j) hj hw
                rwa [show j + (i - j) - 1 = i - 1 from by omega] at h
              have hgQ : g ∈ Work.CohomologicalShrinking.pSeries p (FreeGroup X) i := by
                have hgeq : g = w⁻¹ * y := by rw [← hwg]; group
                rw [hgeq]
                exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hwQ) hyQ
              rcases lt_or_eq_of_le hji with hjlt | hjeq
              · rw [Work.CohomologicalShrinking.tauSucc_of_lt hjlt]
                exact Subgroup.mem_sup_right
                  (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hgQ, hg⟩))
              · rw [hjeq] at hg ⊢
                rw [Work.CohomologicalShrinking.tauSucc_of_le (le_refl i)]
                refine Subgroup.mem_sup_right
                  (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_top g⟩))
                exact Work.ProP.lowerCentralSeries_le_pCentralSeries p (FreeGroup X) i hg
    · -- the piece `Q_{i+1}`
      intro y hy
      have hy' : y ∈ Subgroup.map ψ (Work.Shrinking.pCentralSeries p P i) := by
        have h : y ∈ Work.Shrinking.pCentralSeries p (FreeGroup X) i := hy
        rw [← Work.Shrinking.map_pCentralSeries_surjective p ψ hψ i] at h
        exact h
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy'
      refine Subgroup.mem_sup_left (Subgroup.map_mono ?_ (Subgroup.mem_map_of_mem ψ hx))
      exact le_sup_right

/-! ## The target -/

theorem gradedMapMul_surjective (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (Φ : Work.CohomologicalShrinking.OperatorMap G m n) (i j : ℕ) :
    Function.Surjective (Work.CohomologicalShrinking.gradedMapMul p Φ.toHom Φ.surjective i j) := by
  classical
  intro y
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective
    ((refinedTerm p (Work.Shrinking.freeOperatorGroup G n) (tauSucc i j).1
      (tauSucc i j).2).subgroupOf (refinedTerm p (Work.Shrinking.freeOperatorGroup G n) i j)) y
  have hRQ : (y₀ : Work.Shrinking.freeOperatorGroup G n) ∈
      Subgroup.map Φ.toHom (refinedTerm p (Work.Shrinking.freeOperatorGroup G m) i j)
        ⊔ refinedTerm p (Work.Shrinking.freeOperatorGroup G n) (tauSucc i j).1 (tauSucc i j).2 :=
    refinedTerm_le_map_sup_aux p Φ.toHom Φ.surjective i j y₀.2
  haveI : (refinedTerm p (Work.Shrinking.freeOperatorGroup G n) (tauSucc i j).1
      (tauSucc i j).2).Normal := inferInstance
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hRQ
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
  refine ⟨QuotientGroup.mk'
    ((refinedTerm p (Work.Shrinking.freeOperatorGroup G m) (tauSucc i j).1
      (tauSucc i j).2).subgroupOf (refinedTerm p (Work.Shrinking.freeOperatorGroup G m) i j))
    ⟨x, hx⟩, ?_⟩
  rw [Work.CohomologicalShrinking.gradedMapMul_of]
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  change (Φ.toHom x)⁻¹ * (y₀ : Work.Shrinking.freeOperatorGroup G n)
    ∈ refinedTerm p (Work.Shrinking.freeOperatorGroup G n) (tauSucc i j).1 (tauSucc i j).2
  rw [show (Φ.toHom x)⁻¹ * (y₀ : Work.Shrinking.freeOperatorGroup G n) = b from by
        rw [hxa, ← hab]; group]
  exact hb

end Work.SSGRoute
