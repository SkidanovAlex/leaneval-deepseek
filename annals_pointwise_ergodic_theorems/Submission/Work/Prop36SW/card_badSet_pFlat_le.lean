import Mathlib
import Submission.Work.Peluse.Prop36SW.roundDefs
import Submission.Work.Peluse.Prop36SW.szZeroCardLe

/-!
# The Schwartz–Zippel counting bound for the chain's bad set

`Work.Prop36SW.card_badSet_pFlat_le`: for `c ≠ 0`, `Λ ≠ 0` and `m < d`, the number of parameters
`x` in the closed box `Abox D (m+1) H` at which some slot coefficient `pFlat D d c m Λ s` vanishes is
at most `(|D.S (m+1)| · m) · (2H+1)^(nD D (m+1) - 1)`.

The proof: `pFlat D d c m Λ s x` is, as a function of `x`, the evaluation of a **multilinear**
polynomial of total degree `≤ m` (`dirPolyMv`) on the flat parameter space, nonzero because
`Λ ≠ 0`, `d - m ≠ 0`, `c ≠ 0` and the directions of level `≤ m` are nonzero at the constant-`1`
family (`dirOneNatVal_spec`).  The zeros of a nonzero total-degree-`≤ m` polynomial in a box of side
`2H+1` in each of the `nD D (m+1)` variables are then bounded by Schwartz–Zippel
(`szZeroCardIcc`, obtained from the `Fin n` version `szZeroCardLe`), and the union over the
`|D.S (m+1)|` slots gives the stated bound.
-/

namespace Work.Prop36SW

open Work.Peluse.UControl
open Work.Peluse.Prop36SW

noncomputable section

/-- The uncurried index type of the level-`(m+1)` flat parameter space; its cardinality is
`nD D (m+1)`. -/
abbrev ParSigma (D : IdxDatum) (m : ℕ) : Type := Σ i : Fin (m + 1), D.S i

/-- The currying equivalence between the flat parameter space `ParSigma D m → ℤ` and the
`D.Idx`-space of the chain. -/
noncomputable def parCurry (D : IdxDatum) (m : ℕ) : (ParSigma D m → ℤ) ≃ D.Idx (m + 1) :=
  Equiv.piCurry (fun _ _ => ℤ)

lemma parCurry_apply (D : IdxDatum) (m : ℕ) (b : ParSigma D m → ℤ) :
    parCurry D m b = Sigma.curry b := rfl

/-- The product box of side `2H+1` in the uncurried coordinates. -/
noncomputable def boxFinset (D : IdxDatum) (m H : ℕ) : Finset (ParSigma D m → ℤ) :=
  Fintype.piFinset (fun _ : ParSigma D m => Finset.Icc (-(H : ℤ)) (H : ℤ))

/-- The curried parameter family read off an assignment of the uncurried coordinates (the levels
`> m` are set to `0`; `D.dir d c j` with `j ≤ m` never reads them). -/
def curOfParam (D : IdxDatum) (m : ℕ) (a : ParSigma D m → ℤ) : (j : ℕ) → D.S j → ℤ :=
  fun j s => if h : j < m + 1 then a ⟨⟨j, h⟩, s⟩ else 0

/-- The multivariate polynomial (in the uncurried coordinates) whose value at `a` is the level-`j`
direction of the support `w` at the parameter family `curOfParam D m a`.  It is multilinear of
total degree `≤ j`. -/
noncomputable def dirPolyMv (D : IdxDatum) (d : ℕ) (c : ℤ) (m : ℕ) :
    (j : ℕ) → D.I j → MvPolynomial (ParSigma D m) ℤ
  | 0, _ => MvPolynomial.C c
  | (j + 1), w => ∑ s ∈ w.1,
      MvPolynomial.C ((d : ℤ) - (j : ℤ)) * dirPolyMv D d c m j (D.par j s)
        * (if h : j + 1 < m + 1 then MvPolynomial.X ⟨⟨j + 1, h⟩, s⟩ else 0)

lemma eval_dirPolyMv (D : IdxDatum) (d : ℕ) (c : ℤ) (m : ℕ) :
    ∀ (j : ℕ), j ≤ m → ∀ (w : D.I j) (a : ParSigma D m → ℤ),
      MvPolynomial.eval a (dirPolyMv D d c m j w) = D.dir d c j w (curOfParam D m a) := by
  intro j
  induction j with
  | zero =>
    intro hj w a
    simp only [dirPolyMv, IdxDatum.dir, MvPolynomial.eval_C]
  | succ j ih =>
    intro hj w a
    have hlt : j + 1 < m + 1 := by omega
    rw [dirPolyMv, IdxDatum.dir]
    simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, curOfParam, dif_pos hlt]
    rw [Finset.sum_congr rfl (fun s hs => by rw [ih (by omega) (D.par j s) a])]

/-- The (positive) multiplicity of the direction of level `j` at the constant-`1` parameter family:
`dir d c j w (fun _ _ => 1) = c · dirOneNatVal D d j w`. -/
noncomputable def dirOneNatVal (D : IdxDatum) (d : ℕ) : (j : ℕ) → D.I j → ℕ
  | 0, _ => 1
  | (j + 1), w => (d - j) * ∑ s ∈ w.1, dirOneNatVal D d j (D.par j s)

lemma dirOneNatVal_spec (D : IdxDatum) {d : ℕ} {c : ℤ} :
    ∀ (j : ℕ), j < d → ∀ (w : D.I j),
      0 < dirOneNatVal D d j w ∧
      D.dir d c j w (fun _ _ => (1 : ℤ)) = c * ((dirOneNatVal D d j w : ℕ) : ℤ) := by
  intro j
  induction j with
  | zero =>
    intro hj w
    refine ⟨by simp [dirOneNatVal], ?_⟩
    simp [dirOneNatVal, IdxDatum.dir]
  | succ j ih =>
    intro hj w
    have hjlt : j < d := by omega
    constructor
    · rw [dirOneNatVal]
      refine Nat.mul_pos (by omega) (Finset.sum_pos' ?_ ?_)
      · intro s hs
        exact le_of_lt (ih hjlt (D.par j s)).1
      · obtain ⟨s₀, hs₀⟩ := w.2
        exact ⟨s₀, hs₀, (ih hjlt (D.par j s₀)).1⟩
    · rw [IdxDatum.dir, dirOneNatVal]
      simp only [mul_one]
      rw [Finset.sum_congr rfl (fun s _ => by rw [(ih hjlt (D.par j s)).2])]
      push_cast
      rw [Nat.cast_sub (le_of_lt hjlt)]
      rw [show c * (((d : ℤ) - ↑j) * ∑ s ∈ w.1, ↑(dirOneNatVal D d j (D.par j s)))
            = ((d : ℤ) - ↑j) * c * ∑ s ∈ w.1, ↑(dirOneNatVal D d j (D.par j s)) by ring]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => by ring)

lemma dirPolyMv_ne_zero (D : IdxDatum) (d : ℕ) (c : ℤ) (m : ℕ) (hc : c ≠ 0) (hd : m < d) :
    ∀ (j : ℕ), j ≤ m → ∀ (w : D.I j), dirPolyMv D d c m j w ≠ 0 := by
  intro j hj w hzero
  have hev := eval_dirPolyMv D d c m j hj w (fun _ : ParSigma D m => (1 : ℤ))
  rw [hzero, map_zero] at hev
  have hne : D.dir d c j w (curOfParam D m (fun _ => (1:ℤ))) ≠ 0 := by
    rw [Work.Peluse.dir_congr D d c j w (curOfParam D m fun _ => (1:ℤ)) (fun _ _ => (1:ℤ))
      (fun j' hj' s => by simp only [curOfParam]; rw [dif_pos (by omega)])]
    have hjlt : j < d := by omega
    obtain ⟨hpos, hid⟩ := dirOneNatVal_spec (D := D) (d := d) (c := c) j hjlt w
    rw [hid]
    exact mul_ne_zero hc (Nat.cast_ne_zero.mpr hpos.ne')
  exact hne hev.symm

lemma totalDegree_dirPolyMv (D : IdxDatum) (d : ℕ) (c : ℤ) (m : ℕ) :
    ∀ (j : ℕ), j ≤ m → ∀ (w : D.I j), (dirPolyMv D d c m j w).totalDegree ≤ j := by
  intro j
  induction j with
  | zero =>
    intro hj w
    simp only [dirPolyMv, MvPolynomial.totalDegree_C, le_refl]
  | succ j ih =>
    intro hj w
    have hlt : j + 1 < m + 1 := by omega
    rw [dirPolyMv]
    simp only [dif_pos hlt]
    refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le (fun s hs => ?_))
    have hp : (dirPolyMv D d c m j (D.par j s)).totalDegree ≤ j := ih (by omega) (D.par j s)
    have hterm : (MvPolynomial.C ((d : ℤ) - (j : ℤ)) * dirPolyMv D d c m j (D.par j s)
        * MvPolynomial.X (⟨⟨j + 1, hlt⟩, s⟩ : ParSigma D m)).totalDegree ≤ j + 1 := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_X]
      have h2 : (MvPolynomial.C ((d : ℤ) - (j : ℤ)) *
          dirPolyMv D d c m j (D.par j s)).totalDegree ≤ j := by
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        rw [MvPolynomial.totalDegree_C, zero_add]
        exact hp
      omega
    exact hterm

/-- **Schwartz–Zippel for an arbitrary finite variable type and the box `[-H, H]`.**  Obtained from
the `Fin n` version `szZeroCardLe` by reindexing the variables along `Fintype.equivFin`. -/
theorem szZeroCardIcc {σ : Type*} [Fintype σ] [DecidableEq σ] {D H : ℕ}
    (p : MvPolynomial σ ℤ) (hp : p ≠ 0) (hdeg : p.totalDegree ≤ D) (hH : 1 ≤ H) :
    ((Fintype.piFinset (fun _ : σ => Finset.Icc (-(H : ℤ)) (H : ℤ))).filter
      (fun a => MvPolynomial.eval a p = 0)).card ≤ D * (2 * H + 1) ^ (Fintype.card σ - 1) := by
  classical
  set e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ with he
  have hp' : p.rename e ≠ 0 := by
    intro h
    apply hp
    have h2 := congrArg (MvPolynomial.rename e.symm) h
    simpa [MvPolynomial.rename_rename, Equiv.symm_comp_self] using h2
  have hdeg' : (p.rename e).totalDegree ≤ D :=
    le_trans (MvPolynomial.totalDegree_rename_le e p) hdeg
  have hsz := szZeroCardLe (n := Fintype.card σ) (D := D) (H := H + 1)
    (p.rename e) hp' hdeg' (by omega)
  have hbox : Finset.Ioo (-(((H + 1 : ℕ) : ℤ))) (((H + 1 : ℕ) : ℤ))
      = Finset.Icc (-(H : ℤ)) (H : ℤ) := by
    ext x; simp only [Finset.mem_Ioo, Finset.mem_Icc]; omega
  have hcard : ((Fintype.piFinset (fun _ : σ => Finset.Icc (-(H : ℤ)) (H : ℤ))).filter
        (fun a => MvPolynomial.eval a p = 0)).card
      = ((Fintype.piFinset (fun _ : Fin (Fintype.card σ) =>
          Finset.Ioo (-(((H + 1 : ℕ) : ℤ))) (((H + 1 : ℕ) : ℤ)))).filter
        (fun f => MvPolynomial.eval f (p.rename e) = 0)).card := by
    rw [hbox]
    refine Finset.card_bij (fun a _ => fun i => a (e.symm i)) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Fintype.mem_piFinset] at ha ⊢
      refine ⟨fun i => ha.1 _, ?_⟩
      rw [MvPolynomial.eval_rename,
        show (fun i => a (e.symm i)) ∘ e = a by funext v; simp [e]]
      exact ha.2
    · intro a1 ha1 a2 ha2 h
      funext v
      have := congrFun h (e v)
      simpa [e] using this
    · intro g hg
      simp only [Finset.mem_filter, Fintype.mem_piFinset] at hg
      refine ⟨fun v => g (e v), ?_, ?_⟩
      · simp only [Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨fun v => hg.1 _, ?_⟩
        change (MvPolynomial.eval (g ∘ e)) p = 0
        rw [← MvPolynomial.eval_rename e g p]
        exact hg.2
      · ext i
        simp [e]
  rw [hcard]
  refine le_trans hsz ?_
  rw [show 2 * (H + 1) - 1 = 2 * H + 1 by omega]

theorem card_badSet_pFlat_le (D : Work.Peluse.UControl.IdxDatum) (d m Λ H : ℕ) (c : ℤ)
    (hc : c ≠ 0) (hΛ : Λ ≠ 0) (hd : m < d) (hH : 1 ≤ H) :
    ((Work.Peluse.Prop36SW.Abox D (m + 1) H).filter (fun x => ∃ s : D.S (m + 1),
        Work.Peluse.Prop36SW.pFlat D d c m Λ s x = 0)).card
      ≤ (Fintype.card (D.S (m + 1)) * m)
        * (2 * H + 1) ^ (Work.Peluse.Prop36SW.nD D (m + 1) - 1)
:= by
  classical
  -- the evaluation of the flat polynomial at a slot coefficient
  have hflat : ∀ (s : D.S (m + 1)) (b : ParSigma D m → ℤ),
      MvPolynomial.eval b (MvPolynomial.C ((Λ : ℤ) * ((d : ℤ) - (m : ℤ))) *
          dirPolyMv D d c m m (D.par m s))
        = pFlat D d c m Λ s (encD D (m + 1) (parCurry D m b)) := by
    intro s b
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C,
      eval_dirPolyMv D d c m m le_rfl (D.par m s) b]
    have h1 : D.pad (m + 1) (parCurry D m b) = curOfParam D m b := by
      funext j s'
      simp only [curOfParam, IdxDatum.pad, parCurry_apply, Sigma.curry]
    have h2 : decD D (m + 1) (encD D (m + 1) (parCurry D m b)) = parCurry D m b :=
      decD_encD D (m + 1) _
    rw [pFlat, h2, h1]
  -- the box in the uncurried coordinates is the `parBox`
  have hmem : ∀ b : ParSigma D m → ℤ,
      b ∈ boxFinset D m H ↔ parCurry D m b ∈ D.parBox (m + 1) H := by
    intro b
    rw [boxFinset, Fintype.mem_piFinset, IdxDatum.mem_parBox]
    simp only [Finset.mem_Icc]
    constructor
    · intro h j s; exact h ⟨j, s⟩
    · intro h v; exact h v.1 v.2
  -- change of variables from `parBox` to the product box
  have hkey : ((D.parBox (m + 1) H).filter (fun a => ∃ s : D.S (m + 1),
        pFlat D d c m Λ s (encD D (m + 1) a) = 0)).card
      = ((boxFinset D m H).filter (fun b => ∃ s : D.S (m + 1),
        pFlat D d c m Λ s (encD D (m + 1) (parCurry D m b)) = 0)).card := by
    refine Finset.card_bij (fun a _ => (parCurry D m).symm a) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter] at ha ⊢
      refine ⟨?_, ?_⟩
      · rw [hmem, Equiv.apply_symm_apply]; exact ha.1
      · rw [Equiv.apply_symm_apply]; exact ha.2
    · intro a1 ha1 a2 ha2 h
      exact (parCurry D m).symm.injective h
    · intro b hb
      simp only [Finset.mem_filter] at hb
      refine ⟨parCurry D m b, ?_, (parCurry D m).symm_apply_apply b⟩
      simp only [Finset.mem_filter]
      exact ⟨(hmem b).mp hb.1, hb.2⟩
  -- replace `pFlat` by the evaluation of the polynomial
  have hpoly : ((boxFinset D m H).filter (fun b => ∃ s : D.S (m + 1),
        pFlat D d c m Λ s (encD D (m + 1) (parCurry D m b)) = 0))
      = ((boxFinset D m H).filter (fun b => ∃ s : D.S (m + 1),
        MvPolynomial.eval b (MvPolynomial.C ((Λ : ℤ) * ((d : ℤ) - (m : ℤ))) *
          dirPolyMv D d c m m (D.par m s)) = 0)) := by
    refine Finset.filter_congr (fun b _ => ?_)
    exact exists_congr (fun s => by rw [hflat s b])
  -- Schwartz–Zippel for each slot
  have hsz : ∀ s : D.S (m + 1),
      ((boxFinset D m H).filter (fun b => MvPolynomial.eval b
        (MvPolynomial.C ((Λ : ℤ) * ((d : ℤ) - (m : ℤ))) *
          dirPolyMv D d c m m (D.par m s)) = 0)).card
      ≤ m * (2 * H + 1) ^ (Fintype.card (ParSigma D m) - 1) := by
    intro s
    have hne : (MvPolynomial.C ((Λ : ℤ) * ((d : ℤ) - (m : ℤ))) *
        dirPolyMv D d c m m (D.par m s)) ≠ 0 := by
      refine mul_ne_zero (MvPolynomial.C_ne_zero.mpr ?_)
        (dirPolyMv_ne_zero D d c m hc hd m le_rfl (D.par m s))
      exact mul_ne_zero (by exact_mod_cast hΛ) (by intro hh; omega)
    have hdeg : (MvPolynomial.C ((Λ : ℤ) * ((d : ℤ) - (m : ℤ))) *
        dirPolyMv D d c m m (D.par m s)).totalDegree ≤ m := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      exact totalDegree_dirPolyMv D d c m m le_rfl (D.par m s)
    rw [boxFinset]
    exact szZeroCardIcc _ hne hdeg hH
  -- the union bound over the slots
  have hub : ((boxFinset D m H).filter (fun b => ∃ s : D.S (m + 1),
        MvPolynomial.eval b (MvPolynomial.C ((Λ : ℤ) * ((d : ℤ) - (m : ℤ))) *
          dirPolyMv D d c m m (D.par m s)) = 0)).card
      ≤ (Fintype.card (D.S (m + 1)) * m) * (2 * H + 1) ^ (nD D (m + 1) - 1) := by
    have heq : ((boxFinset D m H).filter (fun b => ∃ s : D.S (m + 1),
          MvPolynomial.eval b (MvPolynomial.C ((Λ : ℤ) * ((d : ℤ) - (m : ℤ))) *
            dirPolyMv D d c m m (D.par m s)) = 0))
        = (Finset.univ : Finset (D.S (m + 1))).biUnion (fun s => (boxFinset D m H).filter
            (fun b => MvPolynomial.eval b (MvPolynomial.C ((Λ : ℤ) * ((d : ℤ) - (m : ℤ))) *
              dirPolyMv D d c m m (D.par m s)) = 0)) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hb, s, hs⟩; exact ⟨s, hb, hs⟩
      · rintro ⟨s, hb, hs⟩; exact ⟨hb, s, hs⟩
    rw [heq]
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum (fun s _ => hsz s)) ?_
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [show nD D (m + 1) = Fintype.card (ParSigma D m) from rfl]
    exact le_of_eq (by ring_nf)
  calc ((Abox D (m + 1) H).filter (fun x => ∃ s : D.S (m + 1),
        pFlat D d c m Λ s x = 0)).card
      = ((D.parBox (m + 1) H).filter (fun a => ∃ s : D.S (m + 1),
          pFlat D d c m Λ s (encD D (m + 1) a) = 0)).card := by
        simp only [Abox, Finset.filter_image,
          Finset.card_image_of_injective _ (encD_injective D (m + 1))]
    _ = ((boxFinset D m H).filter (fun b => ∃ s : D.S (m + 1),
          pFlat D d c m Λ s (encD D (m + 1) (parCurry D m b)) = 0)).card := hkey
    _ = ((boxFinset D m H).filter (fun b => ∃ s : D.S (m + 1),
          MvPolynomial.eval b (MvPolynomial.C ((Λ : ℤ) * ((d : ℤ) - (m : ℤ))) *
            dirPolyMv D d c m m (D.par m s)) = 0)).card := congrArg Finset.card hpoly
    _ ≤ (Fintype.card (D.S (m + 1)) * m) * (2 * H + 1) ^ (nD D (m + 1) - 1) := hub

end

end Work.Prop36SW
