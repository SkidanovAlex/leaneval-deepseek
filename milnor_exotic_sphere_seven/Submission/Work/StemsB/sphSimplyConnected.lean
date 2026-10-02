import Mathlib
import Submission.Work.StemsB.concat_telescope
import Submission.Work.StemsB.paths_homotopic_of_contractible
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.pathConnected_band

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The sphere `Sⁿ` is simply connected for `n ≥ 2`

The classical proof: `Sⁿ` (`n ≥ 2`) is covered by the two contractible caps `capA n`, `capB n`
whose intersection is the equatorial band, which is path connected (`Work.Cohomology.pathConnected_band`).
A loop is subdivided using a Lebesgue number of the cover, each piece lands in one of the two
contractible caps, and the resulting concatenation is telescoped away.

* `Work.StemsB.loop_null` — the loop argument;
* `Work.StemsB.simplyConnectedSpace_of_cover` — the two-set (van Kampen) lemma;
* `Work.StemsB.sphSimplyConnected` — the target statement.

## Main result

* `Work.StemsB.sphSimplyConnected`: `SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)`
  for `n ≥ 2`.
-/

open scoped Topology
open Set unitInterval

namespace Work.StemsB

variable {X : Type*} [TopologicalSpace X]
/-- Casting a path twice. -/
lemma Path.cast_cast' {a b : X} (γ : Path a b) {a' b' a'' b'' : X} (hx : a' = a) (hy : b' = b)
    (hx' : a'' = a') (hy' : b'' = b') :
    (γ.cast hx hy).cast hx' hy' = γ.cast (hx'.trans hx) (hy'.trans hy) := by
  ext s
  rfl

/-- A loop in a space covered by two open contractible sets with path-connected intersection is
null-homotopic. -/
theorem loop_null {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    [ContractibleSpace ↥A] [ContractibleSpace ↥B] (hAB : IsPathConnected (A ∩ B))
    {x : X} (γ : Path x x) : γ.Homotopic (Path.refl x) := by
  classical
  -- Lebesgue number
  obtain ⟨ε, hεpos, hε⟩ := lebesgue_number_lemma_of_metric (s := Set.univ)
      (c := fun b : Bool => γ ⁻¹' (if b then B else A)) isCompact_univ
      (fun b => by
        cases b
        · exact hA.preimage γ.continuous
        · exact hB.preimage γ.continuous)
      (by
        intro t _
        rcases (show γ t ∈ A ∪ B by rw [hcover]; exact Set.mem_univ _) with h | h
        · exact Set.mem_iUnion.mpr ⟨false, h⟩
        · exact Set.mem_iUnion.mpr ⟨true, h⟩)
  -- number of pieces
  obtain ⟨N, hNpos, hNlt⟩ : ∃ N : ℕ, 0 < N ∧ (1 : ℝ) / N < ε := by
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
    refine ⟨M + 1, Nat.succ_pos _, ?_⟩
    have hM' : 1 < (M : ℝ) * ε := by
      rw [div_lt_iff₀ hεpos] at hM
      linarith
    rw [div_lt_iff₀ (by positivity)]
    push_cast
    nlinarith [hM', hεpos]
  -- cut points
  let t : Fin (N + 1) → I := fun j => ⟨((j : ℕ) : ℝ) / N, by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    exact_mod_cast (Nat.lt_succ_iff.mp j.isLt)⟩
  have htmono : Monotone t := by
    intro i j hij
    show ((i:ℕ):ℝ)/N ≤ ((j:ℕ):ℝ)/N
    rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < ((N:ℕ):ℝ))]
    exact_mod_cast (Fin.le_iff_val_le_val.mp hij)
  have ht0 : t 0 = 0 := by ext; simp [t]
  have htN : t ⟨N, by omega⟩ = 1 := by
    ext
    simp only [t]
    rw [div_self (by positivity : ((N:ℕ):ℝ) ≠ 0)]
    rfl
  -- pieces lie in A or in B
  have hpiece : ∀ k : Fin N,
      (∀ s, γ.subpath (t k.castSucc) (t k.succ) s ∈ A) ∨
      (∀ s, γ.subpath (t k.castSucc) (t k.succ) s ∈ B) := by
    intro k
    obtain ⟨b, hb⟩ := hε (t k.castSucc) (Set.mem_univ _)
    have hdist : ∀ u : I, t k.castSucc ≤ u → u ≤ t k.succ → dist u (t k.castSucc) < ε := by
      intro u h1 h2
      rw [Subtype.dist_eq, Real.dist_eq]
      have h3 : |((u:ℝ)) - ((t k.castSucc : I):ℝ)| ≤ ((t k.succ : I):ℝ) - ((t k.castSucc : I):ℝ) := by
        rw [abs_sub_le_iff]
        have h1' : ((t k.castSucc : I):ℝ) ≤ (u:ℝ) := h1
        have h2' : (u:ℝ) ≤ ((t k.succ : I):ℝ) := h2
        constructor <;> linarith
      have h4 : ((t k.succ : I):ℝ) - ((t k.castSucc : I):ℝ) = 1 / N := by
        simp only [t]
        rw [div_sub_div_same]
        norm_num
      rw [h4] at h3
      linarith
    have hmem : ∀ u ∈ Set.Icc (t k.castSucc) (t k.succ), γ u ∈ (if b then B else A) := by
      intro u hu
      exact hb (by rw [Metric.mem_ball]; exact hdist u hu.1 hu.2)
    have his : ∀ s, γ.subpath (t k.castSucc) (t k.succ) s ∈ (if b then B else A) := by
      intro s
      have hle' : t k.castSucc ≤ t k.succ := htmono (Fin.le_iff_val_le_val.mpr (by simp))
      show γ (Icc.convexComb (t k.castSucc) (t k.succ) s) ∈ (if b then B else A)
      exact hmem _ ⟨Icc.le_convexComb hle' s, Icc.convexComb_le hle' s⟩
    cases b
    · exact Or.inl (by simpa using his)
    · exact Or.inr (by simpa using his)
  -- type of each piece
  let Ts : Fin N → Set X := fun k =>
    if (∀ s, γ.subpath (t k.castSucc) (t k.succ) s ∈ A) then A else B
  have hTs_mem : ∀ (k : Fin N), ∀ s, γ.subpath (t k.castSucc) (t k.succ) s ∈ Ts k := by
    intro k s
    by_cases h : (∀ s, γ.subpath (t k.castSucc) (t k.succ) s ∈ A)
    · have : Ts k = A := by dsimp only [Ts]; rw [if_pos h]
      rw [this]; exact h s
    · have : Ts k = B := by dsimp only [Ts]; rw [if_neg h]
      rw [this]
      rcases hpiece k with h' | h'
      · exact absurd h' h
      · exact h' s
  have hTs_eq : ∀ k : Fin N, Ts k = A ∨ Ts k = B := by
    intro k
    by_cases h : (∀ s, γ.subpath (t k.castSucc) (t k.succ) s ∈ A)
    · left; dsimp only [Ts]; rw [if_pos h]
    · right; dsimp only [Ts]; rw [if_neg h]
  have hAI : IsPathConnected A :=
    isPathConnected_iff_pathConnectedSpace.mpr (inferInstance : PathConnectedSpace ↥A)
  have hBI : IsPathConnected B :=
    isPathConnected_iff_pathConnectedSpace.mpr (inferInstance : PathConnectedSpace ↥B)
  have hInter : ∀ k l : Fin N, IsPathConnected (Ts k ∩ Ts l) := by
    intro k l
    rcases hTs_eq k with h | h <;> rcases hTs_eq l with h' | h' <;> rw [h, h']
    · simpa using hAI
    · simpa using hAB
    · rw [Set.inter_comm]; simpa using hAB
    · simpa using hBI
  have hTs_contr : ∀ k : Fin N, ContractibleSpace ↥(Ts k) := by
    intro k
    rcases hTs_eq k with h | h
    · rw [h]; infer_instance
    · rw [h]; infer_instance
  -- basepoint
  have hne : (A ∩ B).Nonempty := (isPathConnected_iff.mp hAB).1
  obtain ⟨c, hcA, hcB⟩ := hne
  have hcTs : ∀ k : Fin N, c ∈ Ts k := by
    intro k
    rcases hTs_eq k with h | h <;> rw [h] <;> assumption
  -- endpoints of the pieces
  have hsrc : ∀ k : Fin N, γ (t k.castSucc) ∈ Ts k := by
    intro k
    rw [← Path.source (γ.subpath (t k.castSucc) (t k.succ))]
    exact hTs_mem k 0
  have htgt : ∀ k : Fin N, γ (t k.succ) ∈ Ts k := by
    intro k
    rw [← Path.target (γ.subpath (t k.castSucc) (t k.succ))]
    exact hTs_mem k 1
  -- every cut point lies in the two adjacent types
  have hend : ∀ (j : Fin (N+1)) (k : Fin N),
      ((k:ℕ) = (j:ℕ) ∨ (k:ℕ) + 1 = (j:ℕ)) → γ (t j) ∈ Ts k := by
    intro j k hk
    rcases hk with hk | hk
    · have hj : j = k.castSucc := Fin.ext hk.symm
      rw [hj]; exact hsrc k
    · have hj : j = k.succ := Fin.ext hk.symm
      rw [hj]; exact htgt k
  -- index clamping
  let jN : Fin (N+1) := ⟨N, by omega⟩
  let kzero : Fin N := ⟨0, hNpos⟩
  let kmax : Fin N := ⟨N-1, by omega⟩
  let jm : Fin (N+1) → Fin N := fun j => ⟨(j:ℕ) - 1, by have := j.isLt; omega⟩
  let jp : Fin (N+1) → Fin N := fun j =>
    if ((j:ℕ) = 0) then kmax else ⟨min (j:ℕ) (N-1), by omega⟩
  have htN' : t jN = 1 := by rw [show jN = ⟨N, by omega⟩ from rfl, htN]
  have he : γ (t jN) = γ (t 0) := by
    rw [htN', ht0]
    exact γ.target.trans γ.source.symm
  have hjm_val : ∀ j : Fin (N+1), ((jm j : Fin N) : ℕ) = (j:ℕ) - 1 := fun j => rfl
  have hjm_succ : ∀ j : Fin (N+1), (j:ℕ) ≠ 0 → (jm j).succ = j := by
    intro j hj
    apply Fin.ext
    rw [Fin.val_succ, hjm_val]
    exact Nat.sub_add_cancel (by omega)
  have hjm_succ' : ∀ k : Fin N, jm k.succ = k := by
    intro k
    apply Fin.ext
    rw [hjm_val]
    simp [Fin.val_succ]
  have hjp_val : ∀ j : Fin (N+1), (j:ℕ) ≠ 0 → (j:ℕ) ≠ N → ((jp j : Fin N) : ℕ) = (j:ℕ) := by
    intro j h0 hN
    have hj : jp j = ⟨min (j:ℕ) (N-1), by omega⟩ := by
      simp only [jp]; rw [if_neg (by simp [h0])]
    rw [hj]; simp only
    exact Nat.min_eq_left (by omega)
  have hjp_castSucc : ∀ k : Fin N, (k:ℕ) ≠ 0 → jp k.castSucc = k := by
    intro k hk
    apply Fin.ext
    rw [hjp_val k.castSucc (by simpa using hk) (by simp [Fin.val_castSucc]; omega)]
    simp [Fin.val_castSucc]
  have hjp_self_castSucc : ∀ j : Fin (N+1), (j:ℕ) ≠ 0 → (j:ℕ) ≠ N → (jp j).castSucc = j := by
    intro j h0 hN
    apply Fin.ext
    rw [Fin.val_castSucc, hjp_val j h0 hN]
  have hjm_zero : jm 0 = kzero := by
    apply Fin.ext; simp only [jm, kzero, Fin.val_zero]
  have hjm_N : jm jN = kmax := by
    apply Fin.ext; simp only [jm, jN, kmax]
  have hjp_zero : jp 0 = kmax := by
    simp only [jp]; rw [if_pos (by simp)]
  have hjp_N : jp jN = kmax := by
    have hj : jp jN = ⟨min ((jN:Fin (N+1)):ℕ) (N-1), by omega⟩ := by
      simp only [jp]; rw [if_neg (by simp only [jN]; omega)]
    rw [hj]; apply Fin.ext
    simp only [jN, kmax]
    exact Nat.min_eq_right (by omega)
  have hsucc_kmax : kmax.succ = jN := by
    apply Fin.ext
    simp only [kmax, jN, Fin.val_succ]
    omega
  let U : Fin (N+1) → Set X := fun j => Ts (jm j) ∩ Ts (jp j)
  have hU_pc : ∀ j : Fin (N+1), IsPathConnected (U j) := fun j => hInter _ _
  have hU_mem : ∀ j : Fin (N+1), γ (t j) ∈ U j := by
    intro j
    by_cases hj0 : (j:ℕ) = 0
    · have hj : j = 0 := Fin.ext (by simpa using hj0)
      rw [hj, show U 0 = Ts kzero ∩ Ts kmax from by simp only [U]; rw [hjm_zero, hjp_zero]]
      refine ⟨hsrc kzero, ?_⟩
      have h := htgt kmax
      rw [hsucc_kmax] at h
      exact he.symm ▸ h
    · by_cases hjN : (j:ℕ) = N
      · have hj : j = jN := Fin.ext (by simpa [jN] using hjN)
        rw [hj, show U jN = Ts kmax ∩ Ts kmax from by simp only [U]; rw [hjm_N, hjp_N]]
        have h := htgt kmax
        rw [hsucc_kmax] at h
        exact ⟨h, h⟩
      · refine ⟨?_, ?_⟩
        · have h := htgt (jm j)
          rw [hjm_succ j hj0] at h
          exact h
        · have h := hsrc (jp j)
          rw [hjp_self_castSucc j hj0 hjN] at h
          exact h
  have hU_c : ∀ j : Fin (N+1), c ∈ U j := fun j => ⟨hcTs _, hcTs _⟩
  -- spine at the basepoint
  have hspine : ∃ p : Path (γ (t 0)) c, ∀ s, p s ∈ U 0 := by
    rcases (hU_pc 0).joinedIn (γ (t 0)) (hU_mem 0) c (hU_c 0) with ⟨p, hp⟩
    exact ⟨p, hp⟩
  let spine : Path (γ (t 0)) c := hspine.choose
  have hspinemem : ∀ s, spine s ∈ U 0 := hspine.choose_spec
  have hspine0 : ∀ s, spine s ∈ Ts kzero := by
    intro s
    rw [← hjm_zero]
    exact (hspinemem s).1
  have hspineN : ∀ s, spine s ∈ Ts kmax := by
    intro s
    rw [← hjp_zero]
    exact (hspinemem s).2
  -- the family δ
  have hδ_exists : ∀ j : Fin (N+1), ∃ p : Path (γ (t j)) c, ∀ s, p s ∈ U j := by
    intro j
    rcases (hU_pc j).joinedIn (γ (t j)) (hU_mem j) c (hU_c j) with ⟨p, hp⟩
    exact ⟨p, hp⟩
  have hcast0 : ∀ j : Fin (N+1), (j:ℕ) = 0 → γ (t j) = γ (t 0) := fun j h => by
    rw [show j = 0 from Fin.ext (by simpa using h)]
  have hcastN : ∀ j : Fin (N+1), (j:ℕ) = N → γ (t j) = γ (t 0) := fun j h => by
    rw [show t j = t jN from by rw [show j = jN from Fin.ext (by simpa [jN] using h)]]
    exact he
  let δ : (j : Fin (N+1)) → Path (γ (t j)) c := fun j =>
    if h : (j:ℕ) = 0 then Path.cast spine (hcast0 j h) rfl
    else if h' : (j:ℕ) = N then Path.cast spine (hcastN j h') rfl
    else (hδ_exists j).choose
  have hδ0 : δ 0 = spine := by
    simp only [δ]
    rw [dif_pos (show ((0:Fin (N+1)):ℕ) = 0 from rfl)]
    rfl
  have hδN : δ jN = Path.cast spine he rfl := by
    simp only [δ]
    rw [dif_neg (by simp only [jN, Fin.val_mk]; omega),
        dif_pos (show ((jN:Fin (N+1)):ℕ) = N from rfl)]
  have hδ_l : ∀ k : Fin N, ∀ s, δ k.castSucc s ∈ Ts k := by
    intro k s
    by_cases hk : (k:ℕ) = 0
    · have hk0 : k = kzero := Fin.ext (by simpa [kzero] using hk)
      rw [hk0] at *
      rw [show kzero.castSucc = 0 from rfl, hδ0]
      exact hspine0 s
    · have h : δ k.castSucc = (hδ_exists k.castSucc).choose := by
        simp only [δ]
        rw [dif_neg (by simpa using hk), dif_neg (by simp only [Fin.val_castSucc]; omega)]
      rw [h]
      have h3 : U k.castSucc ⊆ Ts k := by
        intro y hy
        have hy' : y ∈ Ts (jm k.castSucc) ∩ Ts (jp k.castSucc) := hy
        rw [hjp_castSucc k hk] at hy'
        exact hy'.2
      exact h3 ((hδ_exists k.castSucc).choose_spec s)
  have hδ_r : ∀ k : Fin N, ∀ s, δ k.succ s ∈ Ts k := by
    intro k s
    by_cases hk : (k:ℕ) + 1 = N
    · have hkj : k.succ = jN := Fin.ext (by simpa [jN] using hk)
      rw [hkj, hδN]
      have hU : ∀ y, y ∈ U jN → y ∈ Ts k := by
        intro y hy
        have hy' : y ∈ Ts kmax ∩ Ts kmax := by
          rw [← show U jN = Ts kmax ∩ Ts kmax from by simp only [U]; rw [hjm_N, hjp_N]]
          exact hy
        have hk' : kmax = k := Fin.ext (by simp [kmax]; omega)
        rw [hk'] at hy'
        exact hy'.2
      have hsp : spine s ∈ U jN := by
        rw [show U jN = Ts kmax ∩ Ts kmax from by simp only [U]; rw [hjm_N, hjp_N]]
        exact ⟨hspineN s, hspineN s⟩
      exact hU (spine s) hsp
    · have h : δ k.succ = (hδ_exists k.succ).choose := by
        simp only [δ]
        rw [dif_neg (by simp only [Fin.val_succ]; omega), dif_neg (by simp only [Fin.val_succ]; omega)]
      rw [h]
      have h3 : U k.succ ⊆ Ts k := by
        intro y hy
        have hy' : y ∈ Ts (jm k.succ) ∩ Ts (jp k.succ) := hy
        rw [hjm_succ' k] at hy'
        exact hy'.1
      exact h3 ((hδ_exists k.succ).choose_spec s)
  -- telescoping
  have htel := concat_telescope N (p := γ ∘ t)
    (F := fun k : Fin N => γ.subpath (t k.castSucc) (t k.succ)) (c := c) (δ := δ)
    (fun k => by
      refine paths_homotopic_of_contractible (T := Ts k) (fun s => hTs_mem k s) ?_
      intro s
      rw [Path.trans_apply]
      split_ifs
      · exact hδ_l k _
      · exact hδ_r k _)
  -- the two ends cancel
  have hlast : (Fin.last N : Fin (N+1)) = jN := rfl
  have hcast1 : (δ 0).trans ((δ jN).symm) = (spine.trans spine.symm).cast rfl he := by
    rw [hδ0, hδN]
    apply Path.ext
    funext s
    rfl
  have hcancel : ((spine.trans spine.symm)).Homotopic (Path.refl (γ (t 0))) :=
    ⟨(Path.Homotopy.reflTransSymm spine).symm⟩
  have hH : (γ.subpath (t 0) (t jN)).Homotopic ((Path.refl (γ (t 0))).cast rfl he) := by
    have h1 : (Path.concat (γ ∘ t) (fun k : Fin N => γ.subpath (t k.castSucc) (t k.succ))).Homotopic
        (γ.subpath (t 0) (t jN)) := Path.Homotopic.concat_subpath γ t
    have h3 : (Path.concat (γ ∘ t) (fun k : Fin N => γ.subpath (t k.castSucc) (t k.succ))).Homotopic
        ((δ 0).trans ((δ jN).symm)) := htel
    have h5 : ((δ 0).trans ((δ jN).symm)).Homotopic
        ((spine.trans spine.symm).cast rfl he) := by
      rw [hcast1]
    have h4 : ((spine.trans spine.symm).cast rfl he).Homotopic
        ((Path.refl (γ (t 0))).cast rfl he) := Path.Homotopic.pathCast hcancel rfl he
    exact (h1.symm.trans (h3.trans h5)).trans h4
  -- convert to γ ≃ refl x
  have hsub : (γ.subpath (t 0) (t jN)).cast (congrArg γ ht0).symm (congrArg γ htN').symm =
      γ.subpath 0 1 := by
    apply Path.ext
    funext s
    rw [Path.cast_coe]
    show γ (Icc.convexComb (t 0) (t jN) s) = γ (Icc.convexComb 0 1 s)
    rw [ht0, htN']
  have hH' := Path.Homotopic.pathCast hH (congrArg γ ht0).symm (congrArg γ htN').symm
  rw [hsub] at hH'
  have hq : ((Path.refl (γ (t 0))).cast rfl he).cast (congrArg γ ht0).symm (congrArg γ htN').symm =
      (Path.refl x).cast γ.source γ.target := by
    apply Path.ext
    funext s
    exact (congrArg γ ht0).trans γ.source
  rw [hq] at hH'
  rw [Path.subpath_zero_one] at hH'
  have hfin := Path.Homotopic.pathCast hH' γ.source.symm γ.target.symm
  rw [Path.cast_cast', Path.cast_cast', Path.cast_rfl_rfl, Path.cast_rfl_rfl] at hfin
  exact hfin
/-- **Two-set (van Kampen) lemma.** If `X = A ∪ B` with `A`, `B` open and contractible and `A ∩ B`
path connected, then `X` is simply connected. -/
theorem simplyConnectedSpace_of_cover {A B : Set X} (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) [ContractibleSpace ↥A] [ContractibleSpace ↥B]
    (hAB : IsPathConnected (A ∩ B)) : SimplyConnectedSpace X := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨?_, fun x γ => loop_null hA hB hcover hAB γ⟩
  have h1 : IsPathConnected (A ∪ B) :=
    IsPathConnected.union
      (isPathConnected_iff_pathConnectedSpace.mpr inferInstance)
      (isPathConnected_iff_pathConnectedSpace.mpr inferInstance)
      hAB.nonempty
  rw [pathConnectedSpace_iff_univ]
  rwa [← hcover]

/-- **The unit sphere `Sⁿ ⊆ ℝ^(n+1)` is simply connected for `n ≥ 2`.** -/
theorem sphSimplyConnected (n : ℕ) (hn : 2 ≤ n) :
    SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  have hopenA : IsOpen (Work.Cohomology.capA n) := by
    have hc : Continuous (fun x : ↥(Work.Cohomology.sphSet (n + 1)) => x.1 (Fin.last n)) := by
      fun_prop
    exact hc.isOpen_preimage _ isOpen_Ioi
  have hopenB : IsOpen (Work.Cohomology.capB n) := by
    have hc : Continuous (fun x : ↥(Work.Cohomology.sphSet (n + 1)) => x.1 (Fin.last n)) := by
      fun_prop
    exact hc.isOpen_preimage _ isOpen_Iio
  have hcover : Work.Cohomology.capA n ∪ Work.Cohomology.capB n = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    show x.1 (Fin.last n) > -(1/2) ∨ x.1 (Fin.last n) < 1/2
    by_contra h
    push_neg at h
    linarith [h.1, h.2]
  have hpc : IsPathConnected (Work.Cohomology.capA n ∩ Work.Cohomology.capB n) :=
    isPathConnected_iff_pathConnectedSpace.mpr (Work.Cohomology.pathConnected_band n hn)
  haveI := Work.Cohomology.contractibleSpace_capA n
  haveI := Work.Cohomology.contractibleSpace_capB n
  have hmain : SimplyConnectedSpace ↥(Work.Cohomology.sphSet (n + 1)) :=
    simplyConnectedSpace_of_cover hopenA hopenB hcover hpc
  have heq := Work.Cohomology.sphere_eq_sphSet (n + 1)
  exact heq.symm ▸ hmain

end Work.StemsB
