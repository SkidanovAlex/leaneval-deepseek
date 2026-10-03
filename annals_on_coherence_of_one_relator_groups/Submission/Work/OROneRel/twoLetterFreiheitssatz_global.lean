import Mathlib
import Submission.Work.OROneRel.globalGauge
import Submission.Work.OROneRel.globalGaugeProps
import Submission.Work.OROneRel.ker_gaugeMap_le_winTree
import Submission.Work.OROneRel.mem_normalClosure_singleton
import Submission.Work.OROneRel.normalClosure_finite_subset
import Submission.Work.OROneRel.gaugeExt_hwalk
import Submission.Work.OROneRel.gaugeExt_bedge_gt
import Submission.Work.OROneRel.gaugeExt_bedge_lt
import Submission.Work.OROneRel.cohom_gaugeExt
import Submission.Work.OROneRel.exists_window_of_finite
import Submission.Work.OROneRel.mk_mul_map_keepList_mem
import Submission.Work.OROneRel.exists_killTree_proj
import Submission.Work.OROneRel.winRoot_pow
import Submission.Work.OROneRel.winRho_winRoot
import Submission.Work.OROneRel.walkWord_step_up
import Submission.Work.OROneRel.wordOf_pow_flatten
import Submission.Work.OROneRel.decor_flatten_replicate_gen
import Submission.Work.OROneRel.lsig_wordOf_eq_zero
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.levelChain
import Submission.Work.OROneRel.map_mem_closure

set_option maxHeartbeats 4000000

/-!
# The band Freiheitssatz for the global gauge

For the weight `c = tlW p q` and a global gauge `Wt'` whose trivial edges are the `a`-edges outside
the band together with the band tree, the class map `winRho` identifies `F (β) / ⟪winRoot ^ l⟫` with
a subgroup of `G = ⟨a,b | (a^p b^q)^l⟩`.  This file proves that statement for the *global* gauge
`gaugeExt p q hq Wt`; the transport to an arbitrary band gauge `Wt` (which agrees with `gaugeExt` on
the band) is carried out in the target file.

The proof follows `Submission/Work/OROneRel/NOTES_twoLetter_freiheitssatz_chain.md`: the element `x`
is lifted to the edge group of the level graph, the lift is compared with an explicit product of
conjugates of the walk words (`yLift`), the difference lies in the kernel of the gauge map, hence (by
`ker_gaugeMap_le_winTree`) in the normal closure of the trivial edges, hence — by the window chain
`trivTree_chain` — in the normal closure of the band tree and the walk word at level `0`; projecting
onto `β` (killing the band tree) gives the conclusion.
-/

namespace Work.OROneRel

noncomputable section

/-- `winRho` is the gauge map precomposed with the inclusion of the non-tree edges. -/
theorem winRho_eq_gaugeMap_global {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    winRho Wt c lo hi =
      (gaugeMap Wt c).comp
        (FreeGroup.map (Subtype.val : winBeta Wt c lo hi → α × ℤ)) := by
  refine FreeGroup.ext_hom _ _ fun e => ?_
  simp only [MonoidHom.comp_apply, FreeGroup.map.of, winRho_of, gaugeMap_of]
  rfl

/-- The walk word of `tlU p q ^ l` at level `N` is the `l`-th power of the walk word of `tlU p q`. -/
theorem walkWord_pow {p q l : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (N : ℤ) :
    FreeGroup.mk (decor (tlW p q) N (wordOf (tlU p q ^ l))) = (FreeGroup.mk (decor (tlW p q) N (wordOf (tlU p q)))) ^ l :=
  mk_decor_tlU_pow p q l hp hq N

/-- The walk of `tlU p q ^ l` at level `N` traverses only edges of the window `[N, N + pq]`. -/
theorem walkWord_supported {p q l : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (N : ℤ) :
    ∀ e ∈ decor (tlW p q) N (wordOf (tlU p q ^ l)), coverEdge e ∈ Wedge p q N (N + (p : ℤ) * (q : ℤ)) := by
  intro e he
  rw [wordOf_pow_flatten (tlU p q) l (tlU_isCyclicallyReduced p q hp hq)] at he
  rw [decor_flatten_replicate_at (tlW p q) (wordOf (tlU p q))
    (lsig_wordOf_eq_zero (tlW p q) (tlU p q) (cohom_tlW_tlU p q)) N] at he
  obtain ⟨Y, hY, hYmem⟩ := List.mem_flatten.mp he
  rw [List.mem_replicate] at hY
  obtain ⟨-, rfl⟩ := hY
  -- the decorated walk of `tlU p q` at level `N` stays in `[N, N+pq]`
  rw [decor_tlU_tlW_at] at hYmem
  rcases List.mem_append.mp hYmem with h | h
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
    simp only [coverEdge]
    rw [mem_Wedge_zero]
    have hj : (j : ℤ) + 1 ≤ (p : ℤ) := by
      exact_mod_cast (by have := j.isLt; omega)
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
    have hq0 : (0 : ℤ) ≤ (q : ℤ) := by positivity
    constructor <;> nlinarith
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp h
    simp only [coverEdge]
    rw [mem_Wedge_one]
    have hk : (k : ℤ) + 1 ≤ (q : ℤ) := by
      exact_mod_cast (by have := k.isLt; omega)
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
    have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
    constructor <;> nlinarith


/-- **The band Freiheitssatz, for a gauge whose trivial edges are the band tree plus the `a`-edges
outside the band.**  The gauge `Wt'` is a variable here, so that all the statements below are
syntactic in it; the instantiation with `gaugeExt p q hq Wt` is a separate (one-line) step. -/
theorem twoLetterFreiheitssatz_of_gauge {p q l : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {Wt Wt' : ℤ → FreeGroup (Fin 2)}
    (hW0' : Wt' 0 = 1)
    (hcoh' : ∀ i : ℤ, cohom (tlW p q) (Wt' i) = Multiplicative.ofAdd i)
    (hwalk' : ∀ j : ℤ, ∀ e ∈ decor (tlW p q) 0 (wordOf (Wt' j)),
      coverClassAt Wt' (tlW p q) (coverEdge e) = 1)
    (hband : ∀ e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)),
      coverClassAt Wt' (tlW p q) e = coverClassAt Wt (tlW p q) e)
    (hbgt : ∀ {j : ℤ}, (p : ℤ) * (q : ℤ) < j →
      coverClassAt Wt' (tlW p q) ((1 : Fin 2), j) ≠ 1)
    (hblt : ∀ {j : ℤ}, j ≤ (p : ℤ) - 1 →
      coverClassAt Wt' (tlW p q) ((1 : Fin 2), j) ≠ 1)
    (hcu : cohom (tlW p q) (tlU p q) = 1)
    (hwin : ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    ∀ x : FreeGroup (winBeta Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))),
      winRho Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) x ∈
          Subgroup.normalClosure ({tlU p q ^ l} : Set (FreeGroup (Fin 2))) →
        x ∈ Subgroup.normalClosure
          ({winRoot Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q) ^ l} :
            Set (FreeGroup (winBeta Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))))) := by
  classical
  intro x hx
  -- the lift of `x` to the edge group
  set xLift : FreeGroup (Fin 2 × ℤ) :=
    FreeGroup.map (Subtype.val : winBeta Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) → Fin 2 × ℤ) x
    with hxLift
  have hΦ : gaugeMap Wt' (tlW p q) xLift = winRho Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) x := by
    rw [hxLift, winRho_eq_gaugeMap_global]
    rfl
  have hΦmem : gaugeMap Wt' (tlW p q) xLift ∈
      Subgroup.normalClosure ({tlU p q ^ l} : Set (FreeGroup (Fin 2))) := by
    rw [hΦ]; exact hx
  obtain ⟨n, g, ε, hdec⟩ := mem_normalClosure_singleton hΦmem
  -- the lifts of the conjugators
  set m : Fin n → ℤ := fun i => (cohom (tlW p q) (g i)).toAdd with hm
  set k : Fin n → FreeGroup (Fin 2) := fun i => g i * (Wt' (m i))⁻¹ with hk
  have hg_eq : ∀ i : Fin n, g i = k i * Wt' (m i) := by
    intro i; rw [hk]; group
  have hgk : ∀ i : Fin n, cohom (tlW p q) (g i) = Multiplicative.ofAdd (m i) := by
    intro i; rw [hm]; rfl
  have hkker : ∀ i : Fin n, cohom (tlW p q) (k i) = 1 := by
    intro i
    rw [hk, map_mul, map_inv, hcoh' (m i), hgk i]
    simp
  -- the lift of the relation
  set yLift : FreeGroup (Fin 2 × ℤ) :=
    (List.ofFn fun i : Fin n =>
      FreeGroup.mk (decor (tlW p q) 0 (wordOf (k i))) *
        (FreeGroup.mk (decor (tlW p q) (m i) (wordOf (tlU p q ^ l)))) ^ (ε i) *
        (FreeGroup.mk (decor (tlW p q) 0 (wordOf (k i))))⁻¹).prod with hyLift
  have hwalk0 : ∀ i : Fin n,
      gaugeMap Wt' (tlW p q) (FreeGroup.mk (decor (tlW p q) 0 (wordOf (k i)))) = k i := by
    intro i
    rw [gauge_decor, mk_wordOf, hW0', one_mul, lsig_wordOf, hkker i]
    simp [hW0']
  have hwalkm : ∀ i : Fin n,
      gaugeMap Wt' (tlW p q) (FreeGroup.mk (decor (tlW p q) (m i) (wordOf (tlU p q ^ l)))) =
      Wt' (m i) * (tlU p q ^ l) * (Wt' (m i))⁻¹ := by
    intro i
    rw [gauge_decor, mk_wordOf]
    have hzero : lsig (tlW p q) (wordOf (tlU p q ^ l)) = 0 := by
      rw [lsig_wordOf]
      have : cohom (tlW p q) (tlU p q ^ l) = 1 := by rw [map_pow, hcu, one_pow]
      rw [this]; rfl
    have : m i + lsig (tlW p q) (wordOf (tlU p q ^ l)) = m i := by rw [hzero, add_zero]
    rw [this]
  have hŷgauge : gaugeMap Wt' (tlW p q) yLift = gaugeMap Wt' (tlW p q) xLift := by
    rw [hyLift, hdec, map_list_prod, List.map_ofFn]
    apply congrArg List.prod
    rw [List.ofFn_injective.eq_iff]
    funext i
    simp only [Function.comp_apply]
    rw [map_mul, map_mul, map_inv, map_zpow, hwalk0 i, hwalkm i]
    rw [show (Wt' (m i) * (tlU p q ^ l) * (Wt' (m i))⁻¹) ^ (ε i) =
        Wt' (m i) * (tlU p q ^ l) ^ (ε i) * (Wt' (m i))⁻¹ from by
      rw [conj_zpow]]
    rw [hg_eq i]
    group
  -- the difference lies in the kernel
  have hz : xLift * yLift⁻¹ ∈ Subgroup.normalClosure
      (FreeGroup.of '' {e : Fin 2 × ℤ | coverClassAt Wt' (tlW p q) e = 1}) := by
    refine ker_gaugeMap_le_winTree hW0' hcoh' hwalk' ?_
    rw [map_mul, map_inv, hŷgauge, mul_inv_cancel]
  obtain ⟨T', hT'sub, hT'fin, hzT'⟩ := normalClosure_finite_subset hz
  -- the window
  obtain ⟨A₀, B₀, hA₀, hB₀, hT'W⟩ := exists_window_of_finite p q T' hT'fin
  have hsum : ∀ i : Fin n, |m i| ≤ ∑ j : Fin n, |m j| :=
    fun i => Finset.single_le_sum (fun j _ => abs_nonneg (m j)) (Finset.mem_univ i)
  set A : ℤ := min 0 (min A₀ (-(∑ j : Fin n, |m j|))) with hAdef
  set B : ℤ := max ((p : ℤ) * (q : ℤ)) (max B₀ ((∑ j : Fin n, |m j|) + (p : ℤ) * (q : ℤ)))
    with hBdef
  have hA0 : A ≤ 0 := by rw [hAdef]; exact min_le_left _ _
  have hA0' : A ≤ A₀ := by
    rw [hAdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hAm : ∀ i : Fin n, A ≤ m i := by
    intro i
    have h1 : -(∑ j : Fin n, |m j|) ≤ m i := by
      have := hsum i
      have h2 : -(∑ j : Fin n, |m j|) ≤ -|m i| := neg_le_neg this
      linarith [neg_abs_le (m i)]
    exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) h1
  have hB0 : (p : ℤ) * (q : ℤ) ≤ B := by rw [hBdef]; exact le_max_left _ _
  have hB0' : B₀ ≤ B := by
    rw [hBdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hBm : ∀ i : Fin n, m i + (p : ℤ) * (q : ℤ) ≤ B := by
    intro i
    have h1 : m i ≤ ∑ j : Fin n, |m j| := le_trans (le_abs_self (m i)) (hsum i)
    exact le_trans (by linarith) (le_trans (le_max_right _ _) (le_max_right _ _))
  -- the relators
  have hŷmem : yLift ∈ Subgroup.normalClosure
      (Set.range fun i : Fin n =>
        FreeGroup.mk (decor (tlW p q) (m i) (wordOf (tlU p q ^ l)))) := by
    rw [hyLift]
    refine Subgroup.list_prod_mem (Subgroup.normalClosure (Set.range fun i : Fin n =>
      FreeGroup.mk (decor (tlW p q) (m i) (wordOf (tlU p q ^ l))))) fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    have h1 : (FreeGroup.mk (decor (tlW p q) (m i) (wordOf (tlU p q ^ l)))) ^ (ε i) ∈
        Subgroup.normalClosure (Set.range fun i : Fin n =>
          FreeGroup.mk (decor (tlW p q) (m i) (wordOf (tlU p q ^ l)))) :=
      Subgroup.zpow_mem _ (Subgroup.subset_normalClosure (Set.mem_range_self i)) (ε i)
    have hnorm := Subgroup.normalClosure_normal
      (s := Set.range fun i : Fin n =>
        FreeGroup.mk (decor (tlW p q) (m i) (wordOf (tlU p q ^ l))))
    simpa only [mul_assoc] using hnorm.conj_mem
        ((FreeGroup.mk (decor (tlW p q) (m i) (wordOf (tlU p q ^ l)))) ^ (ε i)) h1
        (FreeGroup.mk (decor (tlW p q) 0 (wordOf (k i))))
  have hŷWrel : yLift ∈ Subgroup.normalClosure (WrelGen p q l A B) := by
    apply Subgroup.normalClosure_mono _ hŷmem
    rintro r ⟨i, rfl⟩
    exact ⟨m i, hAm i, hBm i, rfl⟩
  have hzWrel : xLift * yLift⁻¹ ∈ Subgroup.normalClosure
      (FreeGroup.of '' ({e : Fin 2 × ℤ | coverClassAt Wt' (tlW p q) e = 1} ∩ Wedge p q A B)) := by
    apply Subgroup.normalClosure_mono _ hzT'
    rintro y ⟨e, he, rfl⟩
    exact ⟨e, ⟨hT'sub he, Wedge_mono p q hA0' hB0' (hT'W he)⟩, rfl⟩
  have hchain : xLift ∈ Subgroup.normalClosure (FreeGroup.of ''
      ({e : Fin 2 × ℤ | coverClassAt Wt' (tlW p q) e = 1} ∩ Wedge p q A B)
      ∪ WrelGen p q l A B) := by
    rw [show xLift = (xLift * yLift⁻¹) * yLift from by group]
    refine Subgroup.mul_mem _ ?_ (Subgroup.normalClosure_mono (Set.subset_union_right ..) hŷWrel)
    have hsub1 : FreeGroup.of '' ({e : Fin 2 × ℤ | coverClassAt Wt' (tlW p q) e = 1}
        ∩ Wedge p q A B) ⊆ FreeGroup.of '' ({e : Fin 2 × ℤ | coverClassAt Wt' (tlW p q) e = 1}
          ∩ Wedge p q A B) ∪ WrelGen p q l A B := Set.subset_union_left
    exact Subgroup.normalClosure_mono hsub1 hzWrel
  -- the walk of `tlU p q ^ l` lies in the window
  have hLwin : ∀ p' ∈ decor (tlW p q) 0 (wordOf (tlU p q ^ l)),
      p'.1 ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
    intro p' hp'
    have := walkWord_supported hp hq 0 p' hp'
    rwa [zero_add] at this
  -- the chain
  have hTsub : winTree Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) ⊆ Wedge p q 0 ((p : ℤ) * (q : ℤ)) := by
    intro e he
    rw [mem_winTree] at he
    rw [mem_Wedge]
    exact he.1
  have hbgt' : ∀ {j : ℤ}, (p : ℤ) * (q : ℤ) < j →
      coverClassAt Wt' (tlW p q) ((1 : Fin 2), j) ≠ 1 := fun {j} hj => hbgt hj
  have hblt' : ∀ {j : ℤ}, j ≤ (p : ℤ) - 1 →
      coverClassAt Wt' (tlW p q) ((1 : Fin 2), j) ≠ 1 := fun {j} hj => hblt hj
  have hbandTree : xLift ∈ Subgroup.normalClosure (FreeGroup.of ''
      ({e : Fin 2 × ℤ | coverClassAt Wt' (tlW p q) e = 1} ∩ Wedge p q 0 ((p : ℤ) * (q : ℤ)))
      ∪ {FreeGroup.mk (decor (tlW p q) 0 (wordOf (tlU p q ^ l)))}) := by
    have hyW : xLift ∈ Subgroup.closure (FreeGroup.of '' Wedge p q 0 ((p : ℤ) * (q : ℤ))) := by
      rw [hxLift]
      exact map_mem_closure_of
        (Subtype.val : winBeta Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) → Fin 2 × ℤ)
        (Wedge p q 0 ((p : ℤ) * (q : ℤ))) (fun e => winBeta_val_mem e) x
    exact trivTree_chain (p := p) (q := q) (l := l) hp (hq := hq) (Wt' := Wt')
      (T₀ := winTree Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))) (hT₀ := rfl) (hT₀sub := hTsub)
      (hbgt := hbgt) (hblt := hblt) (hA := hA0) (hB := hB0) (hy := hyW) (hy' := hchain)
  -- the projection
  obtain ⟨π, hπ1, hπ2⟩ := exists_killTree_proj Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))
  have hπtree : ∀ y ∈ Subgroup.normalClosure (treeSet Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))),
      π y = 1 := by
    have hle : Subgroup.normalClosure (treeSet Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))) ≤ π.ker :=
      Subgroup.normalClosure_le_normal fun y hy => by
        change π y = 1; exact hπ1 y hy
    intro y hy
    exact hle hy
  have hπx : π xLift = x := by rw [hxLift]; exact hπ2 x
  have hπW : π (FreeGroup.mk (decor (tlW p q) 0 (wordOf (tlU p q ^ l)))) =
      (winRoot Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q)) ^ l := by
    have hkeep := mk_mul_map_keepList_mem Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))
      (decor (tlW p q) 0 (wordOf (tlU p q ^ l))) hLwin
    have hkr : FreeGroup.mk (keepList Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))
        (decor (tlW p q) 0 (wordOf (tlU p q ^ l)))) =
        (winRoot Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q)) ^ l := by
      rw [← winRoot_eq_mk_keepList]
      exact winRoot_pow Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q) l
        (tlU_isCyclicallyReduced p q hp hq) (cohom_tlW_tlU p q)
    have hPa : π (FreeGroup.mk (decor (tlW p q) 0 (wordOf (tlU p q ^ l))) *
          (FreeGroup.map (Subtype.val : winBeta Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) → Fin 2 × ℤ)
            (FreeGroup.mk (keepList Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))
              (decor (tlW p q) 0 (wordOf (tlU p q ^ l))))))⁻¹) =
        π (FreeGroup.mk (decor (tlW p q) 0 (wordOf (tlU p q ^ l)))) *
          (π (FreeGroup.map
            (Subtype.val : winBeta Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) → Fin 2 × ℤ)
            (FreeGroup.mk (keepList Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))
              (decor (tlW p q) 0 (wordOf (tlU p q ^ l)))))))⁻¹ := by
      rw [map_mul, map_inv]
    have h2 : π (FreeGroup.map
        (Subtype.val : winBeta Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) → Fin 2 × ℤ)
        (FreeGroup.mk (keepList Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))
          (decor (tlW p q) 0 (wordOf (tlU p q ^ l)))))) =
        FreeGroup.mk (keepList Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))
          (decor (tlW p q) 0 (wordOf (tlU p q ^ l)))) := hπ2 _
    have h1 : π (FreeGroup.mk (decor (tlW p q) 0 (wordOf (tlU p q ^ l))) *
          (FreeGroup.map (Subtype.val : winBeta Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) → Fin 2 × ℤ)
            (FreeGroup.mk (keepList Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))
              (decor (tlW p q) 0 (wordOf (tlU p q ^ l))))))⁻¹) = 1 :=
      hπtree _ hkeep
    rw [hPa, h2] at h1
    exact (mul_inv_eq_one.mp h1).trans hkr
  -- the equality of the tree generators with the window tree
  have hTree_eq : FreeGroup.of '' ({e : Fin 2 × ℤ | coverClassAt Wt' (tlW p q) e = 1}
      ∩ Wedge p q 0 ((p : ℤ) * (q : ℤ)))
      = treeSet Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
    rw [trivTree_band']
    rfl
  have hbandTree' : xLift ∈ Subgroup.normalClosure (treeSet Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))
      ∪ {FreeGroup.mk (decor (tlW p q) 0 (wordOf (tlU p q ^ l)))}) := by
    rwa [hTree_eq] at hbandTree
  -- the projection kills the tree and carries the walk word to `winRoot ^ l`
  have hmap : (Subgroup.normalClosure (treeSet Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))
      ∪ {FreeGroup.mk (decor (tlW p q) 0 (wordOf (tlU p q ^ l)))} :
        Set (FreeGroup (Fin 2 × ℤ)))).map π ≤
      Subgroup.normalClosure ({(winRoot Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q)) ^ l} :
        Set (FreeGroup (winBeta Wt' (tlW p q) 0 ((p : ℤ) * (q : ℤ))))) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine Subgroup.normalClosure_le_normal fun y hy => ?_
    rcases hy with hy | hy
    · refine Subgroup.mem_comap.mpr ?_
      rw [hπtree y (Subgroup.subset_normalClosure hy)]
      exact Subgroup.one_mem _
    · refine Subgroup.mem_comap.mpr ?_
      rw [Set.mem_singleton_iff] at hy
      rw [hy, hπW]
      exact Subgroup.subset_normalClosure (Set.mem_singleton _)
  rw [← hπx]
  exact hmap (Subgroup.mem_map_of_mem π hbandTree')

end

end Work.OROneRel
