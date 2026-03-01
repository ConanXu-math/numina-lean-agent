import Optlib.Algorithm.AdaptiveADMM.AdaptiveLemmas
import Optlib.Algorithm.AdaptiveADMM.AdaptiveScheme
import Optlib.Convex.ImageSubgradientClosed
import Optlib.Algorithm.AdaptiveADMM.AdaptiveInv_bounded
import Optlib.Algorithm.AdaptiveADMM.AdaptiveCondition2
noncomputable section

open Set InnerProductSpace Topology Filter Bornology Metric Real

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F]

variable(admm : ADMM E₁ E₂ F)

namespace AdaptiveADMM_Convergence_Proof

variable {admm admm_kkt}

local notation "f₁" => admm.f₁
local notation "f₂" => admm.f₂
local notation "A₁" => admm.A₁
local notation "A₂" => admm.A₂
local notation "x₁" => admm.x₁
local notation "x₂" => admm.x₂
local notation "b" => admm.b
local notation "y"  => admm.y
local notation "τ"  => admm.τ
local notation "ρₙ" => admm.ρₙ
local notation "ρmin" => admm.ρmin
local notation "x₁'" => admm_kkt.x₁
local notation "x₂'" => admm_kkt.x₂
local notation "y'"  => admm_kkt.y
local notation "A₁†" => ContinuousLinearMap.adjoint A₁
local notation "A₂†" => ContinuousLinearMap.adjoint A₂
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

section

-- variable [Setting E₁ E₂ F admm admm_kkt]
-- lemma g_is_nonneg [Condition_C2 admm admm_kkt]: ∀ n : ℕ , g n ≥ 0 := by
--    intro n
--    have h:  0 ≤ ‖ey n‖^2 := by exact sq_nonneg ‖ey n‖
--    have := sq_nonneg ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖
--    have h1: 0 ≤ τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by exact mul_nonneg  (HWY_thm4_1_ineq' n) this
--    have h2:= admm.htau.1
--    have h3:= sq_pos_of_pos (admm.hρₙ_pos n)
--    have h4 : 0 ≤  τ * ρₙ n^2 := by linarith[mul_pos h2 h3]
--    have h5 := sq_nonneg ‖A₂ (e₂ n)‖
--    have h6 : 0 ≤ τ * ρₙ n^2  * ‖A₂ (e₂ n)‖^2 := by exact mul_nonneg h4 h5
--    simp [g]
--    linarith


lemma g2_bd_above [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]: ∃ C : ℝ, ∀ n : ℕ, g2 n < C := by
   have := HWY_ineq_55_nat
   rcases this with ⟨C, hC_pos, hC⟩
   use C + 1
   intro n
   have h := hC n
   linarith

lemma g2_isBounded' [Condition_C2  admm admm_kkt] [IsOrderedMonoid ℝ]: ∃ (r : ℝ), (range g2) ⊆ ball 0 r := by
   rcases g2_bd_above with ⟨C,bd⟩
   use C; intro x hx; simp; rw [range] at hx; simp at hx
   rcases hx with ⟨n,eq⟩; rw [← eq, abs_eq_self.2]; exact bd n
   apply g2_nonneg

lemma g2_isBounded [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]: IsBounded (range g2) := (isBounded_iff_subset_ball 0).2  g2_isBounded'

lemma ey_isBounded' [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]: ∃ (r : ℝ), (range ey) ⊆ ball 0 r := by
   rcases g2_bd_above with ⟨r, g2_isBounded⟩;
   rcases admm.rho_upper_bound with ⟨BU, hBU⟩;
   use √(r*BU^2); intro x hx; simp; rw [range] at hx; simp at hx
   rcases hx with ⟨n, eq⟩; rw [← eq]
   have h1 := g2_nonneg n
   have h2:  0 ≤ τ * ‖ey n‖^2 := by exact mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg ‖ey n‖)
   have h3: 0 ≤ ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by exact sq_nonneg ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖
   have : 0 ≤ T_HWY - τ := by linarith [HWY_thm4_1_ineq]
   have h4 : 0 ≤ τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
      apply mul_nonneg
      apply mul_nonneg
      exact le_of_lt admm.htau.1
      exact this
      exact h3
   have h6 : 0 ≤ τ * ‖A₂ (e₂ n)‖^2 := by exact mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg ‖A₂ (e₂ n)‖)
   have h7 := g2_isBounded n
   have h8: 1/BU^2 * ‖ey n‖^2 ≤ 1/ρₙ n^2 * ‖ey n‖^2 := by
      gcongr
      exact sq_pos_of_pos (admm.hρₙ_pos n)
      exact hBU.2 n
   have h9: 1/BU^2 * ‖ey n‖^2 ≤ g2 n := by
      simp [g2]
      simp at h8
      linarith
   have h10: 1/BU^2 * ‖ey n‖^2 < r := by
      linarith
   have h10': ‖ey n‖^2 / BU^2 < r := by
      rw [div_eq_mul_one_div]
      convert h10 using 1
      ring
   have h11: ‖ey n‖^2 < r * BU^2 := by
      exact (div_lt_iff₀ (sq_pos_of_pos hBU.1)).mp h10'
   have h12: ‖ey n‖ < √(r * BU^2) := by
      have h13 : √(‖ey n‖ ^ 2) = ‖ey n‖ := by rw [pow_two]; apply Real.sqrt_mul_self; apply norm_nonneg
      rw [← h13]
      have : ‖ey n‖ ^ 2 ≥ 0 := by apply pow_two_nonneg
      apply (Real.sqrt_lt_sqrt_iff this).mpr
      exact h11
   exact h12

lemma ey_isBounded [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]: IsBounded (range ey ) := (isBounded_iff_subset_ball 0).2  ey_isBounded'


lemma A₂e₂_isBounded' [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]: ∃ (r : ℝ), (range (A₂ ∘ e₂) ) ⊆ ball 0 r := by
   rcases g2_bd_above with ⟨r, g2_isBounded⟩;
   rcases admm.rho_upper_bound with ⟨BU, hBU⟩;
   use √(r/τ); intro x hx; simp; rw [range] at hx; simp at hx
   rcases hx with ⟨n, eq⟩; rw [← eq]
   have h1 := g2_nonneg n
   have h2: 0 ≤ 1/ρₙ n^2 * ‖ey n‖^2 := by
      have h2': 0 ≤ 1/ρₙ n^2 := by
         apply div_nonneg
         linarith
         linarith [sq_pos_of_pos (admm.hρₙ_pos n)]
      have h2'': 0 ≤ ‖ey n‖^2 := by exact sq_nonneg ‖ey n‖
      exact mul_nonneg h2' h2''
   have h3: 0 ≤ ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by exact sq_nonneg ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖
   have : 0 ≤ T_HWY - τ := by linarith [HWY_thm4_1_ineq]
   have h4 : 0 ≤ τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
      apply mul_nonneg
      apply mul_nonneg
      exact le_of_lt admm.htau.1
      exact this
      exact h3
   have h6 : 0 ≤ τ * ‖A₂ (e₂ n)‖^2 := by exact mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg ‖A₂ (e₂ n)‖)
   have h7 := g2_isBounded n
   have h5 :τ * ‖A₂ (e₂ n)‖^2 ≤ g2 n := by
      simp [g2]
      simp at h2
      linarith
   have h8:  ‖A₂ (e₂ n)‖^2 * τ< r := by
      linarith
   have h9: ‖A₂ (e₂ n)‖^2 < r / τ := by
      have := (lt_div_iff₀ (admm.htau.1)).mpr h8
      linarith
   have h10: ‖A₂ (e₂ n)‖ < √(r / τ) := by
      have h11: √(‖A₂ (e₂ n)‖ ^ 2) = ‖A₂ (e₂ n)‖ := by rw [pow_two]; apply Real.sqrt_mul_self; apply norm_nonneg
      rw [← h11]
      have : ‖A₂ (e₂ n)‖ ^ 2 ≥ 0 := by apply pow_two_nonneg
      apply (Real.sqrt_lt_sqrt_iff this).mpr
      exact h9
   exact h10

lemma A₂e₂_isBounded [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]: IsBounded (range (A₂ ∘ e₂) ) :=
   (isBounded_iff_subset_ball 0).2 A₂e₂_isBounded'

lemma A₁e₁_A₂e₂_equation_c2 [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : ∀ n : ℕ, ‖A₁ (e₁ n) + A₂ (e₂ n)‖ = ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ := by
   intro n
   have : A₁ (e₁ n) + A₂ (e₂ n) = A₁ (x₁ n) + A₂ (x₂ n) - b := by
      rw [e₁, e₂]; simp
      calc
         _ = A₁ (x₁ n) + A₂ (x₂ n) - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_sub_comm]
         _ = A₁ (x₁ n) + A₂ (x₂ n) - b + b - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_cancel]
         _ = A₁ (x₁ n) + A₂ (x₂ n) - b := by
            rw [admm_kkt.h.eq]; simp
   rw [this]

lemma A₁e₁_A₂e₂_isBounded'[Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : ∃ (r : ℝ), (range (A₁ ∘ e₁ + A₂ ∘ e₂) ) ⊆ ball 0 r := by
   rcases g2_bd_above with ⟨r, g2_isBounded⟩;
   rcases admm.rho_upper_bound with ⟨BU, hBU⟩;
   use √(r/(τ * (T_HWY - τ))); intro x hx; simp; rw [range] at hx; simp at hx
   rcases hx with ⟨n, eq⟩; rw [← eq]
   have h1 := g2_nonneg n
   have h2: 0 ≤ 1/ρₙ n^2 * ‖ey n‖^2 := by
      have h2': 0 ≤ 1/ρₙ n^2 := by
         apply div_nonneg
         linarith
         linarith [sq_pos_of_pos (admm.hρₙ_pos n)]
      have h2'': 0 ≤ ‖ey n‖^2 := by exact sq_nonneg ‖ey n‖
      exact mul_nonneg h2' h2''
   have h3: 0 < τ * (T_HWY - τ) := by
      apply mul_pos
      exact admm.htau.1
      linarith [HWY_thm4_1_ineq]
   have h4 : 0 ≤ τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
      apply mul_nonneg
      apply mul_nonneg
      exact le_of_lt admm.htau.1
      linarith [HWY_thm4_1_ineq]
      exact sq_nonneg ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖
   have h6 : 0 ≤ τ * ‖A₂ (e₂ n)‖^2 := by exact mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg ‖A₂ (e₂ n)‖)
   have h7 := g2_isBounded n
   have h8 :τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 ≤ g2 n := by
      simp [g2]
      simp at h2
      linarith
   have h9: τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 < r := by
      linarith
   have h10: ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 * (τ * (T_HWY - τ)) < r := by
      linarith
   have h11: ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 < r / (τ * (T_HWY - τ)) := by
      have := (lt_div_iff₀ h3).mpr h10
      linarith
   have h12: ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ < √(r / (τ * (T_HWY - τ))) := by
      have h13: √(‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2) = ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ := by rw [pow_two]; apply Real.sqrt_mul_self; apply norm_nonneg
      rw [← h13]
      have : ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 ≥ 0 := by apply pow_two_nonneg
      gcongr
   have h14: ‖A₁ (e₁ n) + A₂ (e₂ n)‖ < √(r / (τ * (T_HWY - τ))) := by
      have h15: ‖A₁ (e₁ n) + A₂ (e₂ n)‖ = ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ := by rw [A₁e₁_A₂e₂_equation_c2]
      rw [h15]
      exact h12
   exact h14

lemma A₁e₁_A₂e₂_isBounded [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]: IsBounded (range (A₁ ∘ e₁ + A₂ ∘ e₂) ) :=
   (isBounded_iff_subset_ball 0).2 A₁e₁_A₂e₂_isBounded'

lemma A₁e₁_isBounded' [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]: ∃ (r : ℝ), range (A₁ ∘ e₁) ⊆ ball 0 r := by

   have h_A₂e₂ : ∃ r1, range (A₂ ∘ e₂) ⊆ ball 0 r1 := by apply A₂e₂_isBounded'
   rcases h_A₂e₂ with ⟨r1, h_A₂e₂⟩

   have h_A₁e₁_A₂e₂ : ∃ r2, range (A₁ ∘ e₁ + A₂ ∘ e₂) ⊆ ball 0 r2 := by apply A₁e₁_A₂e₂_isBounded'
   rcases h_A₁e₁_A₂e₂ with ⟨r2, h_A₁e₁_A₂e₂⟩

   let r := r1 + r2
   have hr : r = r1 + r2 := by rfl
   use r

   intros x hx
   rcases hx with ⟨n, rfl⟩

   have h : ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ < r1 + r2 := by
      have ha : ‖A₂ (e₂ n)‖ < r1 := by
         have haa : A₂ (e₂ n) ∈ range (A₂ ∘ e₂) := by use n; simp
         have ha_in_ball : A₂ (e₂ n) ∈ Metric.ball 0 r1 := by apply h_A₂e₂ haa
         rw [Metric.mem_ball, dist_zero_right] at ha_in_ball
         exact ha_in_ball
      have hb : ‖A₁ (e₁ n) + A₂ (e₂ n)‖ < r2 := by
         have hbb : A₁ (e₁ n) + A₂ (e₂ n) ∈ range (A₁ ∘ e₁ + A₂ ∘ e₂) := by use n; simp
         have hb_in_ball : A₁ (e₁ n) + A₂ (e₂ n) ∈ Metric.ball 0 r2 := by apply h_A₁e₁_A₂e₂ hbb
         rw [Metric.mem_ball, dist_zero_right] at hb_in_ball
         exact hb_in_ball
      linarith

   have h_ineq : ‖A₁ (e₁ n)‖ ≤ ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ := by apply norm_le_add_norm_add

   have h_norm : ‖A₁ (e₁ n)‖ < r := by
      calc ‖A₁ (e₁ n)‖
         _ ≤ ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ := h_ineq
         _ < r1 + r2 := h
         _ = r := hr

   have h_dist : dist (A₁ (e₁ n)) 0 < r := by
      rw[← sub_zero (A₁ (e₁ n))] at h_norm
      rw[SeminormedAddGroup.dist_eq (A₁ (e₁ n)) 0]
      exact h_norm

   rw [← Metric.mem_ball] at h_dist
   apply h_dist

lemma A₁e₁_isBounded [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]: IsBounded (range (A₁ ∘ e₁) ) :=
   (isBounded_iff_subset_ball 0).2 A₁e₁_isBounded'

lemma open_mapping_e₁ [Setting E₁ E₂ F admm admm_kkt] (fullrank₁: Function.Injective admm.A₁):
      ∃ C > 0, ∀ n : ℕ, ‖e₁ n‖ ≤ C * ‖A₁ (e₁ n)‖ := by
   rcases inv_bounded₂ A₁ fullrank₁ with ⟨C, ⟨C_pos,hh⟩⟩
   use C; constructor
   ·  exact C_pos
   ·  intro n; exact hh (e₁ n)

lemma open_mapping_e₂ [Setting E₁ E₂ F admm admm_kkt] (fullrank₂: Function.Injective admm.A₂):
      ∃ C > 0, ∀ n : ℕ, ‖e₂ n‖ ≤ C * ‖A₂ (e₂ n)‖ := by
   rcases inv_bounded₂ A₂ fullrank₂ with ⟨C, ⟨C_pos,hh⟩⟩
   use C; constructor
   ·  exact C_pos
   ·  intro n; exact hh (e₂ n)

  lemma x₁_isBounded' [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ](fullrank₁: Function.Injective admm.A₁): ∃ (r : ℝ), (range x₁) ⊆ ball 0 r := by
   rcases A₁e₁_isBounded' with ⟨M, h₁⟩
   rcases open_mapping_e₁ fullrank₁ with ⟨C, ⟨C_pos, h₂⟩⟩
   rw [range] at h₁
   use C * M + ‖x₁'‖; intro x hx; rw [range] at hx; simp at hx
   rcases hx with ⟨n,eq⟩
   have A₁e₁_bd : ‖A₁ (e₁ n)‖ < M := by
      have : A₁ (e₁ n) ∈ {x | ∃ n, A₁ (e₁ n) = x} := by simp
      have : A₁ (e₁ n) ∈ ball 0 M := by tauto
      simp at this; exact this
   rw [← eq]; simp
   calc
      _ = ‖(x₁ n - x₁') + x₁'‖ := by rw [add_comm, add_sub, add_comm, add_sub_assoc, sub_self, add_zero]
      _ ≤ ‖x₁ n - x₁'‖ + ‖x₁'‖ := by apply norm_add_le
      _ = ‖e₁ n‖ + ‖x₁'‖ := by rw [e₁]
      _ ≤ C * ‖A₁ (e₁ n)‖ + ‖x₁'‖ := by linarith [h₂ n]
      _ < C * M + ‖x₁'‖ := by linarith [mul_lt_mul_of_pos_left A₁e₁_bd C_pos]

lemma x₁_isBounded [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ](fullrank₁: Function.Injective admm.A₁):
      IsBounded (range x₁) :=
   (isBounded_iff_subset_ball 0).2 (x₁_isBounded' fullrank₁)

lemma x₂_isBounded' [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] (fullrank₂: Function.Injective admm.A₂):
      ∃ (r : ℝ), (range x₂ ) ⊆ ball 0 r := by
   rcases A₂e₂_isBounded' with ⟨M, h₁⟩
   rcases open_mapping_e₂ fullrank₂ with ⟨C, ⟨C_pos, h₂⟩⟩
   rw [range] at h₁
   use C * M + ‖x₂'‖; intro x hx; rw [range] at hx; simp at hx
   rcases hx with ⟨n,eq⟩
   have A₂e₂_bd : ‖A₂ (e₂ n)‖ < M := by
      have : A₂ (e₂ n) ∈ {x | ∃ n, A₂ (e₂ n) = x} := by simp
      have : A₂ (e₂ n) ∈ ball 0 M := by tauto
      simp at this; exact this
   rw [← eq]; simp
   calc
      _ = ‖(x₂ n - x₂') + x₂'‖ := by rw [add_comm, add_sub, add_comm, add_sub_assoc, sub_self, add_zero]
      _ ≤ ‖x₂ n - x₂'‖ + ‖x₂'‖ := by apply norm_add_le
      _ = ‖e₂ n‖ + ‖x₂'‖ := by rw [e₂]
      _ ≤ C * ‖A₂ (e₂ n)‖ + ‖x₂'‖ := by linarith [h₂ n]
      _ < C * M + ‖x₂'‖ := by linarith [mul_lt_mul_of_pos_left A₂e₂_bd C_pos]

lemma x₂_isBounded [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] (fullrank₂: Function.Injective admm.A₂):
      IsBounded (range x₂) :=
   (isBounded_iff_subset_ball 0).2 (x₂_isBounded' fullrank₂)

lemma y_isBounded' [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] :
      ∃ (r : ℝ), (range y) ⊆ ball 0 r := by
   rcases ey_isBounded' with ⟨M, h⟩
   use M + ‖y'‖; intro x hx; rw [range] at hx h; simp at hx; simp
   rcases hx with ⟨n,eq⟩; rw [← eq]
   have ey_bd : ‖ey n‖ < M := by
      have : ey n ∈ {x | ∃ n, ey n = x} := by simp
      have : ey n ∈ ball 0 M := by tauto
      simp at this; exact this
   calc
      _ = ‖(y n) - y' + y'‖ := by rw [add_comm, add_sub, add_comm, add_sub_assoc, sub_self, add_zero]
      _ ≤ ‖y n - y'‖ + ‖y'‖ := by apply norm_add_le
      _ = ‖ey n‖ + ‖y'‖ := by rw [ey]
      _ < M + ‖y'‖ := by linarith

lemma y_isBounded  [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]:  IsBounded (range y) :=
   (isBounded_iff_subset_ball 0).2  y_isBounded'


lemma times_eq : (range (fun n => (x₁ n,  x₂ n, y n ) ))
⊆  (range x₁) ×ˢ  (range x₂) ×ˢ (range y) := by
   simp [range]
   intro x hx
   dsimp at hx
   simp only [mem_prod, mem_setOf_eq]
   rcases hx with ⟨n , hn⟩
   have h1 : x₁ n = x.1 := hn.symm ▸ rfl
   have h2 : x₂ n = x.2.1 := hn.symm ▸ rfl
   have h3 : y  n = x.2.2 := hn.symm ▸ rfl
   exact ⟨ ⟨ n , h1 ⟩, ⟨ n , h2 ⟩, ⟨ n , h3 ⟩⟩


lemma xy_isBounded [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]
      (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂):
      IsBounded (range (fun n => (x₁ n,  x₂ n, y n ) )) := by
   apply IsBounded.subset
   apply IsBounded.prod (x₁_isBounded fullrank₁)
   apply IsBounded.prod (x₂_isBounded fullrank₂) y_isBounded
   apply times_eq

structure Converge_Subseq_2 [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] where
   x₁'' : E₁
   x₂'' : E₂
   y''  : F
   φ    : ℕ → ℕ
   hphi:StrictMono φ
   hconverge:Tendsto (fun n => (x₁ (φ n),  x₂ (φ n), y (φ n))) atTop (𝓝 (x₁'' , x₂'' , y''))

def Subseq_c2 [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]
      (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂): Converge_Subseq_2 := by
   let x := tendsto_subseq_of_bounded (xy_isBounded fullrank₁ fullrank₂)
      (inSet (fun n => (x₁ n,  x₂ n, y n )) )
   choose x hx using x
   choose φ hphi1 using hx.2
   exact
      {
         x₁'' := x.1
         x₂'' := x.2.1
         y''  := x.2.2
         φ   := φ
         hphi:= hphi1.1
         hconverge:=hphi1.2
      }

variable (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂)
-- Subsequence mapping
local notation "φ" => Converge_Subseq_2.φ (Subseq_c2 fullrank₁ fullrank₂)

-- The limit of the subsequence
local notation "x₁''" => Converge_Subseq_2.x₁'' (Subseq_c2 fullrank₁ fullrank₂)
local notation "x₂''" => Converge_Subseq_2.x₂'' (Subseq_c2 fullrank₁ fullrank₂)
local notation "y''"  => Converge_Subseq_2.y'' (Subseq_c2 fullrank₁ fullrank₂)

-- The subsequence mapping is strictly increasing
lemma hphi_StrictMono [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : StrictMono φ := (Subseq_c2 fullrank₁ fullrank₂).hphi

--lim_{n → ∞} (uₙ ,vₙ ) = 0 -> lim_{n → ∞} uₙ  = 0
lemma admm_nhds_prod_eq [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : 𝓝 (x₁'' , x₂'' , y'') = 𝓝 x₁'' ×ˢ 𝓝 x₂'' ×ˢ 𝓝 y'' := by
   rw[nhds_prod_eq,nhds_prod_eq]

lemma hconverge [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]  : Tendsto (fun n => (x₁ (φ n),  x₂ (φ n), y (φ n)))
atTop (𝓝 x₁'' ×ˢ 𝓝 x₂'' ×ˢ 𝓝 y''):=by
   have := (Subseq_c2 fullrank₁ fullrank₂).hconverge
   rw[admm_nhds_prod_eq] at this
   exact this

lemma x₁_subseq_converge [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : Tendsto (fun n => (x₁ (φ n)))  atTop (𝓝 x₁'') :=
   (Filter.tendsto_prod_iff'.1 (hconverge fullrank₁ fullrank₂)).1

lemma x₂_subseq_converge [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : Tendsto (fun n => (x₂ (φ n)))  atTop (𝓝 x₂'') :=
   (Filter.tendsto_prod_iff'.1 (Filter.tendsto_prod_iff'.1 (hconverge fullrank₁ fullrank₂)).2).1

lemma y_subseq_converge  [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : Tendsto (fun n => (y (φ n)))  atTop (𝓝 y'') :=
   (Filter.tendsto_prod_iff'.1 (Filter.tendsto_prod_iff'.1 (hconverge fullrank₁ fullrank₂)).2).2

def φ₂' [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : ℕ → ℕ+ := by
   intro n
   exact (φ (n + 1)).toPNat'

local notation "φ₂" => φ₂' fullrank₁ fullrank₂

lemma φ₂_equ [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : ∀ n : ℕ , φ₂ n = φ (n + 1) := by
   intro n
   have : φ (n + 1) > 0 := by
      calc φ (n + 1)
         _ ≥ n + 1  := StrictMono.id_le (hphi_StrictMono fullrank₁ fullrank₂) (n + 1)
         _ > 0      :=by linarith
   exact Nat.sub_one_add_one_eq_of_pos this

-- lim_{ n → ∞} x_n  = x =>  lim_{ n → ∞} x_{n+1}  = x
lemma x₁_subseq_converge' [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : Tendsto (fun n => (x₁ (φ₂ n)))  atTop (𝓝 x₁'') :=by
   have : (fun n => x₁ (φ₂ n)) = (fun n => (x₁ (φ (n+1)))) :=by
      ext n;rw[φ₂_equ fullrank₁ fullrank₂ n]
   rw[this , Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ x₁ (φ n)) ) 1]
   apply x₁_subseq_converge

lemma x₂_subseq_converge' [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]  : Tendsto (fun n => (x₂ (φ₂ n)))  atTop (𝓝 x₂'') :=by
   have : (fun n => x₂ (φ₂ n)) = (fun n => (x₂ (φ (n+1)))) :=by
      ext n;rw[φ₂_equ fullrank₁ fullrank₂ n]
   rw[this , Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ x₂ (φ n)) ) 1]
   apply x₂_subseq_converge

lemma y_subseq_converge' [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => (y (φ₂ n))) atTop (𝓝 y'') := by
   have : (fun n => y (φ₂ n)) = (fun n => (y (φ (n+1)))) := by
      ext n; rw [φ₂_equ fullrank₁ fullrank₂ n]
   rw[this , Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ y (φ n)) ) 1]
   apply y_subseq_converge
lemma square_converge_zero₁ [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm admm_kkt]  (h : Tendsto (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2)  atTop (𝓝 0)) :
   Tendsto (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖)  atTop (𝓝 0) := by
   have : Tendsto (fun n => √((‖A₁ (x₁ n) + A₂ (x₂ n) - b‖)^2))  atTop (𝓝 √0) := by apply Filter.Tendsto.sqrt h
   rw [Real.sqrt_zero] at this; simp at this; exact this

-- ‖A₁ (e₁ n) + A₂ (e₂ n)‖ → 0
theorem HWY_Convergence_2_residual [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm admm_kkt]:
    Tendsto (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) atTop (nhds 0) := by
  have h_nplus1 := HWY_Convergence_2_residual'
  rw [← tendsto_add_atTop_iff_nat 1]
  exact h_nplus1


lemma converge_zero₁ [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm admm_kkt]: Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖)  atTop (𝓝 0) := by
   have eq : (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖) = (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖) := by
      funext n
      have : A₁ (e₁ n) + A₂ (e₂ n) = A₁ (x₁ n) + A₂ (x₂ n) - b := by
         rw [e₁, e₂]; simp
         calc
            _ = A₁ (x₁ n) + A₂ (x₂ n) - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_sub_comm]
            _ = A₁ (x₁ n) + A₂ (x₂ n) - b + b - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_cancel]
            _ = A₁ (x₁ n) + A₂ (x₂ n) - b := by
               rw [admm_kkt.h.eq]; simp
      rw [this]
   rw [eq]
   have := HWY_Convergence_2_residual
   apply square_converge_zero₁ this

-- ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ → 0
lemma converge_zero₂ [Condition_C2  admm admm_kkt] [IsOrderedMonoid ℝ]: Tendsto (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖)  atTop (𝓝 0) := by
   have eq : (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖) = (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖) := by
      funext n
      have : A₁ (e₁ n) + A₂ (e₂ n) = A₁ (x₁ n) + A₂ (x₂ n) - b := by
         rw [e₁, e₂]; simp
         calc
            _ = A₁ (x₁ n) + A₂ (x₂ n) - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_sub_comm]
            _ = A₁ (x₁ n) + A₂ (x₂ n) - b + b - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_cancel]
            _ = A₁ (x₁ n) + A₂ (x₂ n) - b := by
               rw [admm_kkt.h.eq]; simp
      rw [this]
   rw [← eq]
   exact converge_zero₁

-- with the square norm of A₂ (x₂ (n + 1) - x₂ n) → 0, we can infer that the norm of A₂ (x₂ (n + 1) - x₂ n) also → 0
lemma square_converge_zero₃ [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm admm_kkt] (h : Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖ ^ 2)  atTop (𝓝 0)) :
   Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖)  atTop (𝓝 0) := by
   have : Tendsto (fun n => √((‖A₂ (x₂ (n + 1) - x₂ n)‖)^2))  atTop (𝓝 √0) := by apply Filter.Tendsto.sqrt h
   rw [Real.sqrt_zero] at this; simp [Real.sqrt_sq] at this; simp; exact this

-- the norm of A₂ (x₂ (n + 1) - x₂ n) → 0
theorem converge_zero₃ [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm admm_kkt]:
    Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖)  atTop (𝓝 0) := by
   have : Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖ ^ 2)  atTop (𝓝 0) := by
      have := HWY_Convergence_2_increment
      exact this
   have h := square_converge_zero₃ this
   exact h

-- A₁ (e₁ n) + A₂ (e₂ n) → 0 (Note that this lemma is without the norm)
lemma Seq_converge_zero₁ [Condition_C2  admm admm_kkt] [IsOrderedMonoid ℝ] : Tendsto (fun n => A₁ (e₁ n) + A₂ (e₂ n))  atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2 converge_zero₁

-- A₁ (x₁ n) + A₂ (x₂ n) - b → 0
lemma Seq_converge_zero₂ [Condition_C2  admm admm_kkt] [IsOrderedMonoid ℝ] : Tendsto (fun n => A₁ (x₁ n) + A₂ (x₂ n) - b)  atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2 converge_zero₂

-- A₂ (x₂ (n + 1) - x₂ n) → 0
lemma Seq_converge_zero₃ [Condition_C2  admm admm_kkt] [IsOrderedMonoid ℝ] : Tendsto (fun n => A₂ (x₂ (n + 1) - x₂ n))  atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2 converge_zero₃

-- A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n)) → 0
lemma sub_Seq_converge_zero₁ [Condition_C2  admm admm_kkt] [IsOrderedMonoid ℝ] : Tendsto (fun n => A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n)))
atTop (𝓝 0) := by
   apply Filter.tendsto_iff_seq_tendsto.1 Seq_converge_zero₁
   apply StrictMono.tendsto_atTop
   have : (fun n => (Int.toNat (φ₂ n))) = (fun n => (φ (n+1))) := by
      ext n; rw [φ₂_equ fullrank₁ fullrank₂ n]; simp
   simp at this; rw [this]
   apply StrictMono.comp
   · apply hphi_StrictMono
   · simp [StrictMono]

-- A₁ (x₁ (φ₂ n)) + A₂ (x₂ (φ₂ n)) - b → 0
lemma sub_Seq_converge_zero₂ [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => A₁ (x₁ (φ₂ n)) + A₂ (x₂ (φ₂ n)) - b) atTop (𝓝 0) := by
   apply Filter.tendsto_iff_seq_tendsto.1 Seq_converge_zero₂
   apply StrictMono.tendsto_atTop
   have : (fun n => (Int.toNat (φ₂ n))) = (fun n => (φ (n+1))) := by
      ext n; rw [φ₂_equ fullrank₁ fullrank₂ n]; simp
   simp at this; rw [this]
   apply StrictMono.comp
   · apply hphi_StrictMono
   · simp [StrictMono]

-- A₂ (x₂ ((φ₂ n) + 1) - x₂ (φ₂ n)) → 0
lemma sub_Seq_converge_zero₃ [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm admm_kkt] : Tendsto (fun n => A₂ (x₂ ((φ₂ n) + 1) - x₂ (φ₂ n))) atTop (𝓝 0) := by
   apply Filter.tendsto_iff_seq_tendsto.1 Seq_converge_zero₃
   apply StrictMono.tendsto_atTop
   have : (fun n => (Int.toNat (φ₂ n))) = (fun n => (φ (n+1))) := by
      ext n; rw [φ₂_equ fullrank₁ fullrank₂ n]; simp
   simp at this; rw [this]
   apply StrictMono.comp
   · apply hphi_StrictMono
   · simp [StrictMono]

-- The difference between this lemma and the one above is the change of sub-script.
-- A₂ (x₂ (φ₂ n) - x₂ ((φ₂ n) - 1)) → 0
lemma sub_Seq_converge_zero₃' [Condition_C2  admm admm_kkt] [IsOrderedMonoid ℝ] : Tendsto (fun n => A₂ (x₂ (φ₂ n) - x₂ ((φ₂ n) - 1))) atTop (𝓝 0) := by
   apply Filter.tendsto_iff_seq_tendsto.1 Seq_converge_zero₃
   apply StrictMono.tendsto_atTop
   simp; rw [StrictMono]; intro n₁ n₂ h
   have h₁: φ (n₁ + 1) < φ (n₂ + 1) := by apply hphi_StrictMono; linarith
   have hn₁: φ (n₁ + 1) ≥ 1 := by
      calc
         _ ≥ n₁ + 1 := by apply StrictMono.id_le (hphi_StrictMono fullrank₁ fullrank₂)
         _ ≥ 1 := by linarith
   apply Nat.sub_lt_sub_right hn₁ h₁

-- (( 1 - τ) * ρₙ n ) • (A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n))) → 0
lemma const_smul_subseq₁ [Condition_C2  admm admm_kkt] [IsOrderedMonoid ℝ] : Tendsto (fun n => (( 1 - τ) * ρₙ (φ₂ n) ) • (A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n)))) atTop (𝓝 0) := by
   -- 使用范数性质：‖c • x‖ = |c| * ‖x‖
   have h_norm_eq : (fun n => ‖(( 1 - τ) * ρₙ (φ₂ n) ) • (A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n)))‖) =
                    (fun n => |(1 - τ) * ρₙ (φ₂ n)| * ‖A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n))‖) := by
     ext n
     rw [norm_smul, Real.norm_eq_abs]
   -- 向量序列的范数趋于0
   have h_vector_norm : Tendsto (fun n => ‖A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n))‖) atTop (𝓝 0) := by
     apply tendsto_zero_iff_norm_tendsto_zero.1
     exact sub_Seq_converge_zero₁ fullrank₁ fullrank₂
   -- 使用"有界序列乘以趋于0的序列也趋于0"
   have h_bounded : ∃ C, ∀ n, |(1 - τ) * ρₙ n| ≤ C := by
     rcases admm.rho_upper_bound with ⟨BU, hBU_pos, hBU⟩
     use BU
     intro n
     have h_rho_pos : ρₙ n > 0 := admm.hρₙ_pos n
     have h_rho_bound : ρₙ n ≤ BU := hBU n
     rw [abs_mul]
     -- 由于 ρₙ n > 0，有 |ρₙ n| = ρₙ n
     have h_abs_rho : |ρₙ n| = ρₙ n := abs_of_pos h_rho_pos
     rw [h_abs_rho]
     -- 现在需要证明 |1 - τ| * ρₙ n ≤ BU
     -- 由于 ρₙ n ≤ BU，如果 |1 - τ| ≤ 1，则 |1 - τ| * ρₙ n ≤ 1 * ρₙ n = ρₙ n ≤ BU
     have h_abs_tau_le : |1 - τ| ≤ 1 := by
       have h_tau_pos : τ > 0 := admm.htau.1
       have h_tau_upper : τ < (1 + Real.sqrt 5) / 2 := admm.htau.2
       by_cases h : τ ≤ 1
       · -- 如果 τ ≤ 1，则 1 - τ ≥ 0，所以 |1 - τ| = 1 - τ ≤ 1
         rw [abs_of_nonneg (sub_nonneg.mpr h)]
         linarith
       · -- 如果 τ > 1，则 1 - τ < 0，所以 |1 - τ| = τ - 1
         push_neg at h
         rw [abs_of_neg (sub_neg.mpr h)]
         -- 需要证明 τ - 1 ≤ 1，即 τ ≤ 2
         -- 由于 τ < (1+√5)/2 ≈ 1.618 < 2，所以成立
         have h_tau_lt_2 : τ < 2 := by
           have : (1 + Real.sqrt 5) / 2 < 2 := by
             have h_sqrt5 : Real.sqrt 5 < 3 := by
               -- √5 < 3 因为 5 < 9，所以 √5 < √9 = 3
               have h_sqrt5_lt_sqrt9 : Real.sqrt 5 < Real.sqrt 9 := by
                 apply Real.sqrt_lt_sqrt
                 · norm_num
                 · norm_num
               have h_sqrt9_eq_3 : Real.sqrt 9 = 3 := by norm_num
               linarith [h_sqrt5_lt_sqrt9, h_sqrt9_eq_3]
             linarith
           linarith [h_tau_upper, this]
         linarith
     -- 使用 |1 - τ| * ρₙ n ≤ 1 * ρₙ n = ρₙ n ≤ BU
     calc |1 - τ| * ρₙ n
       ≤ 1 * ρₙ n := mul_le_mul_of_nonneg_right h_abs_tau_le (le_of_lt h_rho_pos)
     _ = ρₙ n := by ring
     _ ≤ BU := h_rho_bound
   rcases h_bounded with ⟨C, hC⟩
   have h_lower : ∀ n, 0 ≤ |(1 - τ) * ρₙ (φ₂ n)| * ‖A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n))‖ := by
     intro n
     apply mul_nonneg
     · exact abs_nonneg _
     · exact norm_nonneg _
   have h_upper : ∀ n, |(1 - τ) * ρₙ (φ₂ n)| * ‖A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n))‖ ≤ C * ‖A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n))‖ := by
     intro n
     apply mul_le_mul_of_nonneg_right (hC (φ₂ n))
     exact norm_nonneg _
   have h_bound_tendsto : Tendsto (fun n => C * ‖A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n))‖) atTop (𝓝 0) := by
     convert Tendsto.const_mul C h_vector_norm using 1
     simp [mul_zero]
   have h_norm_tendsto : Tendsto (fun n => |(1 - τ) * ρₙ (φ₂ n)| * ‖A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n))‖) atTop (𝓝 0) := by
     apply tendsto_of_tendsto_of_tendsto_of_le_of_le
     · exact tendsto_const_nhds
     · exact h_bound_tendsto
     · exact h_lower
     · exact h_upper
   -- 从范数趋于0得到序列趋于0
   apply tendsto_zero_iff_norm_tendsto_zero.2
   rw [h_norm_eq]
   exact h_norm_tendsto

-- ρₙ (φ₂ n) • A₂ (x₂ ((φ₂ n) - 1) - x₂ (φ₂ n))) → 0
lemma const_smul_subseq₂ [Condition_C2  admm admm_kkt] [IsOrderedMonoid ℝ] : Tendsto (fun n => ρₙ (φ₂ n) • A₂ (x₂ ((φ₂ n) - 1) - x₂ (φ₂ n))) atTop (𝓝 0) := by
   have : (fun n => ρₙ (φ₂ n) • A₂ (x₂ ((φ₂ n) - 1) - x₂ (φ₂ n))) = (fun n => (-ρₙ (φ₂ n)) • A₂ (x₂ (φ₂ n) - x₂ ((φ₂ n) - 1))) := by
      ext n
      calc
         _ = ρₙ (φ₂ n) • (-1) • A₂ (x₂ (φ₂ n) - x₂ ((φ₂ n) - 1)) := by simp
         _ = (-ρₙ (φ₂ n)) • A₂ (x₂ (φ₂ n) - x₂ ((φ₂ n) - 1)) := by
            rw [smul_comm, neg_one_smul]; simp
   rw [this]
   apply tendsto_zero_iff_norm_tendsto_zero.2
   rcases admm.rho_upper_bound with ⟨BU, hBU⟩
   have h_vec : Tendsto (fun n => ‖A₂ (x₂ (φ₂ n) - x₂ ((φ₂ n) - 1))‖) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.1
      exact sub_Seq_converge_zero₃' fullrank₁ fullrank₂
   apply tendsto_of_tendsto_of_tendsto_of_le_of_le
   · exact tendsto_const_nhds
   · rw [← mul_zero BU]
     exact Filter.Tendsto.const_mul BU h_vec
   · intro n
     apply norm_nonneg
   · intro n
     simp
     rw [norm_smul]
     gcongr
     have h_pos : ρₙ (φ₂ n) > 0 := admm.hρₙ_pos (φ₂ n)
     have h_bound : ρₙ (φ₂ n) ≤ BU := hBU.2 (φ₂ n)
     -- 由于 ρₙ > 0，有 ‖ρₙ‖ = ρₙ
     have h_norm_eq : ‖ρₙ (φ₂ n)‖ = ρₙ (φ₂ n) := by
       rw [Real.norm_eq_abs, abs_of_pos h_pos]
     rw [h_norm_eq]
     exact h_bound

-- u (φ₂ n) converges to (- A₁† y'')
lemma u_subseq_converge [Condition_C2  admm admm_kkt] [IsOrderedMonoid ℝ] : Tendsto (fun n => u (φ₂ n)) atTop (𝓝 (- A₁† y'')) := by
   have : (fun n => u (φ₂ n)) = (fun n => - A₁† ((y (φ₂ n)) + (( 1 - τ) * ρₙ (φ₂ n) ) • (A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n))) + ρₙ (φ₂ n) • (A₂ (x₂ ((φ₂ n) - 1) - x₂ (φ₂ n))))) := by
      funext n
      rw [u]
   rw [this]
   have : Tendsto (fun n => (y (φ₂ n)) + (( 1 - τ) * ρₙ (φ₂ n) ) • (A₁ (e₁ (φ₂ n))
         + A₂ (e₂ (φ₂ n)))) atTop (𝓝 y'') := by
      rw [← add_zero y'']
      apply Filter.Tendsto.add (y_subseq_converge' fullrank₁ fullrank₂) (const_smul_subseq₁ fullrank₁ fullrank₂)
   have h: Tendsto (fun n => (y (φ₂ n)) + (( 1 - τ) * ρₙ (φ₂ n) ) • (A₁ (e₁ (φ₂ n))
         + A₂ (e₂ (φ₂ n))) + ρₙ (φ₂ n) • (A₂ (x₂ ((φ₂ n) - 1) - x₂ (φ₂ n)))) atTop (𝓝 y'') := by
      rw [← add_zero y'']
      apply Filter.Tendsto.add (this) (const_smul_subseq₂ fullrank₁ fullrank₂)
   have : Tendsto (- A₁†) (𝓝 y'') (𝓝 (- A₁† y'')) := by apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   apply Filter.tendsto_iff_seq_tendsto.1 this; apply h


-- v (φ₂ n) converges to (- A₂† y'')
lemma v_subseq_converge [Condition_C2  admm admm_kkt] [IsOrderedMonoid ℝ] : Tendsto (fun n => v (φ₂ n)) atTop (𝓝 (- A₂† y'')) := by
   have : (fun n => v (φ₂ n)) = (fun n => - A₂† (y (φ₂ n) + (( 1 - τ) * ρₙ (φ₂ n) ) • (A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n))))) := by
      funext n; rw [v]
   rw [this]
   have h: Tendsto (fun n => (y (φ₂ n) + (( 1 - τ) * ρₙ (φ₂ n) ) • (A₁ (e₁ (φ₂ n)) + A₂ (e₂ (φ₂ n))))) atTop (𝓝  y'') := by
      rw [← add_zero y'']
      apply Filter.Tendsto.add (y_subseq_converge' fullrank₁ fullrank₂) (const_smul_subseq₁ fullrank₁ fullrank₂)
   have : Tendsto (- A₂†) (𝓝 y'') (𝓝 (- A₂† y'')) := by apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   apply Filter.tendsto_iff_seq_tendsto.1 this; apply h

-- (nonempty : ∀ (n : ℕ), g n ∈ SubderivAt f (x n)) (lscf : LowerSemicontinuous f)
-- (x_converge : Tendsto x atTop (𝓝 x')) (g_converge : Tendsto g atTop (𝓝 g'))

lemma A₁'y_inthesubgradient [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : - A₁† y'' ∈ SubderivAt f₁ x₁'':=
   Image_subgradient_closed (fun n ↦ u_inthesubgradient (φ₂ n)) admm.lscf₁
   (x₁_subseq_converge' fullrank₁ fullrank₂) (u_subseq_converge   fullrank₁ fullrank₂)

lemma A₂'y_inthesubgradient [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ]  : - A₂† y'' ∈ SubderivAt f₂ x₂'':=
   Image_subgradient_closed (fun n => v_inthesubgradient (φ₂ n)) admm.lscf₂
   (x₂_subseq_converge' fullrank₁ fullrank₂) (v_subseq_converge   fullrank₁ fullrank₂)

-- lim ‖ x_n ‖ = ‖ lim x_n ‖
lemma Satisfying_equational_constraint1' [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : Tendsto A₁ (𝓝 x₁'') (𝓝 (A₁ x₁'')) := by
   apply Continuous.tendsto
   apply ContinuousLinearMap.continuous

lemma Satisfying_equational_constraint1 [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] :
Tendsto (fun n => A₁ (x₁ (φ n))) atTop (𝓝 (A₁ x₁'')) := by
   apply tendsto_iff_seq_tendsto.1 (Satisfying_equational_constraint1' fullrank₁ fullrank₂) (x₁ ∘ φ)
   apply tendsto_iff_seq_tendsto.1 (x₁_subseq_converge fullrank₁ fullrank₂)
   apply StrictMono.tendsto_atTop
   apply strictMono_id

lemma Satisfying_equational_constraint2' [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : Tendsto A₂ (𝓝 x₂'') (𝓝 (A₂ x₂'')) := by
   apply Continuous.tendsto
   apply ContinuousLinearMap.continuous

lemma Satisfying_equational_constraint2 [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] :
Tendsto (fun n => A₂ (x₂ (φ n))) atTop (𝓝 (A₂ x₂'')) := by
   apply tendsto_iff_seq_tendsto.1 (Satisfying_equational_constraint2' fullrank₁ fullrank₂) (x₂ ∘ φ)
   apply tendsto_iff_seq_tendsto.1 (x₂_subseq_converge fullrank₁ fullrank₂)
   apply StrictMono.tendsto_atTop
   apply strictMono_id

lemma Satisfying_equational_constraint' [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] :
Tendsto (fun n => ‖A₁ (x₁ (φ n)) + A₂ (x₂ (φ n)) - b‖) atTop (𝓝 ‖(A₁ x₁'') + (A₂ x₂'') - admm.b‖)
:= by
   apply Tendsto.norm
   apply Tendsto.sub_const
   apply Tendsto.add
   apply Satisfying_equational_constraint1
   apply Satisfying_equational_constraint2

lemma subconverge_zero₂ [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : Tendsto (fun n =>  ‖A₁ (x₁ (φ n)) + A₂ (x₂ (φ n)) - b‖)  atTop (𝓝 0)
:= by
   apply tendsto_iff_seq_tendsto.1 converge_zero₂
   apply StrictMono.tendsto_atTop
   apply hphi_StrictMono

lemma Satisfying_equational_constraint_norm [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] :
      ‖(A₁ x₁'') + (A₂ x₂'') - admm.b‖ = 0 := by
   apply tendsto_nhds_unique (Satisfying_equational_constraint' fullrank₁ fullrank₂)
   apply subconverge_zero₂

lemma Satisfying_equational_constraint [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] :
      (A₁ x₁'') + (A₂ x₂'') = admm.b := by
   have h1 := Satisfying_equational_constraint_norm fullrank₁ fullrank₂
   apply norm_eq_zero.1 at h1
   apply eq_of_sub_eq_zero h1

lemma Iskktpair [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ] : Convex_KKT x₁'' x₂'' y'' admm.toOptProblem :=
   {
      subgrad₁ :=A₁'y_inthesubgradient fullrank₁ fullrank₂
      subgrad₂ :=A₂'y_inthesubgradient fullrank₁ fullrank₂
      eq       :=Satisfying_equational_constraint fullrank₁ fullrank₂
   }

end

variable (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂)
-- Subsequence mapping
local notation "φ" => Converge_Subseq_2.φ (Subseq_c2 fullrank₁ fullrank₂)

-- The point of the subsequence convergence
local notation "x₁''" => Converge_Subseq_2.x₁'' (Subseq_c2 fullrank₁ fullrank₂)
local notation "x₂''" => Converge_Subseq_2.x₂'' (Subseq_c2 fullrank₁ fullrank₂)
local notation "y''"  => Converge_Subseq_2.y'' (Subseq_c2 fullrank₁ fullrank₂)

def admm_kkt_c2 [Condition_C2  admm admm_kkt][IsOrderedMonoid ℝ][_s : Setting E₁ E₂ F admm admm_kkt] :  Existance_of_kkt admm :=
   Existance_of_kkt.mk x₁''  x₂''  y'' (Iskktpair fullrank₁ fullrank₂)

-- e₁ (φ n) → 0
-- x₁ (φ n) → (admm_kkt_c2 fullrank₁ fullrank₂).x₁ = x₁''
lemma e₁_subseq_converge_zero [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (e₁ ∘ φ) atTop (𝓝 0) := by
   have h₁: Tendsto (fun n => (x₁ ∘ φ) n - x₁'') atTop (𝓝 0) := by
      apply tendsto_sub_nhds_zero_iff.2; apply x₁_subseq_converge
   have h₂: (fun n => (x₁ ∘ φ) n - x₁'') = (fun n => e₁ (φ n)) := by
      funext n; rw [e₁];simp; simp [admm_kkt_c2];
   rw [h₂] at h₁; apply h₁

-- e₂ (φ n) → 0
-- x₂ (φ n) → (admm_kkt_c2 fullrank₁ fullrank₂).x₂ = x₂''
lemma e₂_subseq_converge_zero [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (e₂ ∘ φ) atTop (𝓝 0) := by
   have h₁: Tendsto (fun n => (x₂ ∘ φ) n - x₂'') atTop (𝓝 0) := by
      apply tendsto_sub_nhds_zero_iff.2; apply x₂_subseq_converge
   have h₂: (fun n => (x₂ ∘ φ) n - x₂'') = (fun n => e₂ (φ n)) := by
      funext n; rw [e₂]; simp; simp [admm_kkt_c2]
   rw [h₂] at h₁; apply h₁

-- e₂ (φ n) → 0
-- y (φ n) → (admm_kkt_c2 fullrank₁ fullrank₂).y = y''
lemma ey_subseq_converge_zero [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (ey ∘ φ) atTop (𝓝 0) := by
   have h₁: Tendsto (fun n => (y ∘ φ) n - y'') atTop (𝓝 0) := by
      apply tendsto_sub_nhds_zero_iff.2; apply y_subseq_converge
   have h₂: (fun n => (y ∘ φ) n - y'') = (fun n => ey (φ n)) := by
      funext n; rw [ey]; simp; simp [admm_kkt_c2]
   rw [h₂] at h₁; apply h₁

-- ‖ey (φ n)‖ → 0
lemma nrm_ey_subseq_converge_zero [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖ey (φ n)‖) atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.1; apply ey_subseq_converge_zero

-- ‖ey (φ n)‖^2 → 0
lemma sqnrm_ey_subseq_converge_zero [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖ey (φ n)‖^2) atTop (𝓝 0) := by
   rw [← zero_pow]; apply Filter.Tendsto.pow ; apply nrm_ey_subseq_converge_zero; linarith

-- A₁ (e₁ (φ n)) → 0
lemma A₁e₁_subseq_converge_zero [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => A₁ (e₁ (φ n))) atTop (𝓝 0) := by
   have h₁: Tendsto A₁ (𝓝 0) (𝓝 (A₁ 0)) := by
      apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   simp at h₁; apply Filter.tendsto_iff_seq_tendsto.1 h₁; apply e₁_subseq_converge_zero

-- A₂ (e₂ (φ n)) → 0
lemma A₂e₂_subseq_converge_zero [IsOrderedMonoid ℝ][Condition_C2  admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => A₂ (e₂ (φ n))) atTop (𝓝 0) := by
   have h₁: Tendsto A₂ (𝓝 0) (𝓝 (A₂ 0)) := by
      apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   simp at h₁; apply Filter.tendsto_iff_seq_tendsto.1 h₁; apply e₂_subseq_converge_zero

-- ‖A₂ (e₂ (φ n))‖ → 0
lemma nrm_A₂e₂_subseq_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖A₂ (e₂ (φ n))‖) atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.1; apply A₂e₂_subseq_converge_zero

-- ‖A₂ (e₂ (φ n))‖^2 → 0
lemma sqnrm_A₂e₂_subseq_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖A₂ (e₂ (φ n))‖^2) atTop (𝓝 0) := by
   rw [← zero_pow]; apply Filter.Tendsto.pow ; apply nrm_A₂e₂_subseq_converge_zero; linarith


-- A₁ (e₁ (φ n)) + A₂ (e₂ (φ n)) → 0
lemma A₁e₁_A₂e₂_subseq_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))) atTop (𝓝 0) := by
   rw [← add_zero 0]
   apply Tendsto.add (A₁e₁_subseq_converge_zero fullrank₁ fullrank₂) (A₂e₂_subseq_converge_zero fullrank₁ fullrank₂)

-- ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖ → 0
lemma nrm_A₁e₁_A₂e₂_subseq_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖) atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.1; apply A₁e₁_A₂e₂_subseq_converge_zero

-- ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖^2 → 0
lemma sqnrm_A₁e₁_A₂e₂_subseq_converge_zero[IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖^2) atTop (𝓝 0) := by
   rw [← zero_pow]; apply Filter.Tendsto.pow ; apply nrm_A₁e₁_A₂e₂_subseq_converge_zero; linarith



def Q_seq_c2 [Setting E₁ E₂ F admm admm_kkt]: ℕ → ℝ := fun n => ∏ k ∈ Finset.range n, (1 + (θ_k k)^2)

lemma Q_seq_mono_c2 [Setting E₁ E₂ F admm admm_kkt]: Monotone Q_seq_c2 := by
  apply monotone_nat_of_le_succ
  intro n
  dsimp [Q_seq_c2]
  rw [Finset.prod_range_succ]
  have h_factor : 1 ≤ 1 + (θ_k n)^2 := by
    linarith [sq_nonneg (θ_k n)]
  apply le_mul_of_one_le_right
  · apply Finset.prod_nonneg
    intro i _
    linarith [sq_nonneg (θ_k i)]
  · exact h_factor


lemma Q_seq_converges_c2 [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]: ∃ P > 0, Tendsto Q_seq_c2 atTop (𝓝 P) := by
   obtain ⟨S, hS_pos, hS_le⟩ := Condition_C2.one_theta_square_multipliable'
   have h_bdd : BddAbove (range Q_seq_c2) := by
      use S
      rintro _ ⟨n, rfl⟩
      apply le_trans _ hS_le
      cases n with
      | zero =>
         simp [Q_seq_c2]
         apply le_trans (Q_seq_mono_c2 (Nat.zero_le 1))
         exact HWY_ineq_56_1 0
      | succ k =>
         exact HWY_ineq_56_1 k
   have hP := tendsto_atTop_ciSup Q_seq_mono_c2 h_bdd
   use ⨆ i, Q_seq_c2 i
   constructor
   ·  have h0 : Q_seq_c2 0 = 1 := by simp [Q_seq_c2]
      have h_le : 1 ≤ ⨆ i, Q_seq_c2 i := le_trans (le_of_eq h0.symm) (le_ciSup h_bdd 0)
      linarith
   ·  exact hP


def g2_hat [Setting E₁ E₂ F admm admm_kkt]: ℕ → ℝ := fun n => g2 n / Q_seq_c2 n

lemma g2_hat_is_monotone [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+, g2_hat (n+1) ≤ g2_hat n := by
   intro n
   dsimp [g2_hat]
   have h_Q_pos : 0 < Q_seq_c2 n := by
      apply Finset.prod_pos; intro i _; linarith [sq_nonneg (θ_k i)]
   have h_Q_succ_pos : 0 < Q_seq_c2 (n+1) := by
      apply Finset.prod_pos; intro i _; linarith [sq_nonneg (θ_k  i)]
   -- 使用 div_le_div_iff₀，需要两个分母都为正
   rw [div_le_div_iff₀ h_Q_succ_pos h_Q_pos]
   simp [Q_seq_c2]
   rw [Finset.prod_range_succ]
   have h : g2 (n+1) ≤ (1 + (θ_k  n)^2) * g2 n := by
      have := HWY_ineq_56_0 n
      linarith
   have :g2 (n+1) * Q_seq_c2 n
      ≤ ((1 + (θ_k  n)^2) * g2 n) * Q_seq_c2 n := mul_le_mul_of_nonneg_right h (by apply Finset.prod_nonneg; intro i _; linarith [sq_nonneg (θ_k  i)])
   simp [Q_seq_c2] at this
   linarith

-- 证明 g2(φ n) → 0
lemma g2_subseq_converge_zero
      [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))] :
      Tendsto (fun n => g2 (φ n)) atTop (nhds 0) := by
   obtain ⟨BL, hBL_pos, hBL⟩ := admm.rho_lower_bound
   have h_rho_sq : ∀ n, ρₙ (φ n) ^ 2 ≥  BL ^ 2 := fun n => sq_le_sq' (by linarith [admm.hρₙ_pos (φ n)]) (hBL (φ n))
   have h_rho_sq_nonneg : ∀ n, 0 ≤ ρₙ (φ n) ^ 2 := fun n => sq_nonneg (ρₙ (φ n))
   have h1_inner : Tendsto (fun n => ‖ey (φ n)‖^2) atTop (nhds 0) :=
      sqnrm_ey_subseq_converge_zero fullrank₁ fullrank₂
   have h1 :Tendsto (fun n => 1/ρₙ (φ n) ^ 2 * ‖ey (φ n)‖^2) atTop (nhds 0) :=by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      · exact tendsto_const_nhds -- 下界 0
      ·  rw [← mul_zero (1/ BL^2)]
         apply Filter.Tendsto.const_mul (1/ BL^2 ) h1_inner
      ·  intro n
         apply mul_nonneg
         simp [h_rho_sq_nonneg]
         apply sq_nonneg _
      ·  intro n
         simp
         gcongr
         exact hBL (φ n)
   have h2_inner : Tendsto (fun n => ‖A₂ (e₂ (φ n))‖^2) atTop (nhds 0) :=
      sqnrm_A₂e₂_subseq_converge_zero fullrank₁ fullrank₂
   have h2 : Tendsto (fun n => τ * ‖A₂ (e₂ (φ n))‖^2) atTop (nhds 0) := by
      rw [← mul_zero (τ)]
      apply Filter.Tendsto.const_mul (τ) h2_inner
   have h3_inner : Tendsto (fun n => ‖A₁ (x₁ (φ n)) + A₂ (x₂ (φ n)) - b‖^2) atTop (nhds 0) := by
      rw [← zero_pow two_ne_zero]
      apply Tendsto.pow (subconverge_zero₂ fullrank₁ fullrank₂) 2
   have h3 : Tendsto (fun n => τ * (T_HWY - τ)  * ‖A₁ (x₁ (φ n)) + A₂ (x₂ (φ n)) - b‖^2) atTop (nhds 0) := by
      rw [← mul_zero (τ * (T_HWY - τ))]
      apply Filter.Tendsto.const_mul (τ * (T_HWY - τ)) h3_inner
   unfold g2
   have h_add : Tendsto (fun x => 1/ (ρₙ (φ x))^2 * ‖ey (φ x)‖^2 + τ * ‖A₂ (e₂ (φ x))‖^2) atTop (𝓝 (0 + 0)) := by
      apply Tendsto.add h1 h2
   have h_add' : Tendsto (fun x => 1/ (ρₙ (φ x))^2 * ‖ey (φ x)‖^2 + τ * ‖A₂ (e₂ (φ x))‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ (φ x)) + A₂ (x₂ (φ x)) - b‖^2) atTop (𝓝 (0 + 0 + 0)) := by
      apply Tendsto.add h_add h3
   simp at h_add'
   simp
   exact h_add'




-- lemma g_hat_antitone [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt] : Antitone g_hat := by
--    apply antitone_nat_of_succ_le
--    intro n
--    dsimp [g_hat]
--    have h_Q_pos : 0 < Q_seq n := by
--       apply Finset.prod_pos; intro i _; linarith [sq_nonneg (θ_k  i)]
--    have h_Q_succ_pos : 0 < Q_seq (n+1) := by
--       apply Finset.prod_pos; intro i _; linarith [sq_nonneg (θ_k  i)]
--    rw [div_le_div_iff₀ h_Q_succ_pos h_Q_pos]
--    simp [Q_seq]
--    rw [Finset.prod_range_succ]
--    have h_recur := HWY_ineq_52_0 (n.toPNat')
--    have h_step : g (n+1) ≤ (1 + (θ_k  n)^2) * g n := by
--       unfold g
--       have := HWY_ineq_52_0_nat n
--       linarith
--    calc g (n+1) * Q_seq n
--       ≤ ((1 + (θ_k  n)^2) * g n) * Q_seq n := mul_le_mul_of_nonneg_right h_step (by apply Finset.prod_nonneg; intro i _; linarith [sq_nonneg (θ_k  i)])
--    _ = g n * (Q_seq n * (1 + (θ_k  n)^2)) := by ring

lemma g2_hat_isMono [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Antitone (fun n ↦  g2_hat (n + 1)) := by
   apply antitone_nat_of_succ_le
   intro n
   apply g2_hat_is_monotone (n+1).toPNat'

lemma g2_hat_is_nonneg [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ , g2_hat n ≥ 0 := by
   intro n
   dsimp [g2_hat]
   have h_Q_pos : 0 < Q_seq_c2 n := by
      apply Finset.prod_pos; intro i _;have h : 0 < 1 + (θ_k i)^2 := by
         linarith [sq_nonneg (θ_k i)]
      exact h
   have h_g_nonneg : 0 ≤ g2 n := by
      apply g2_nonneg n
   exact div_nonneg h_g_nonneg (by linarith [h_Q_pos])

lemma g2_hat_bddbelow [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      BddBelow (range (fun n ↦ g2_hat (n + 1))) := by
   simp [BddBelow , lowerBounds]
   use 0
   simp only [mem_setOf_eq]
   intro a
   apply g2_hat_is_nonneg (a+1)

lemma g2_hat_ge [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      ∀ n , 0 ≤ (fun _ : ℕ ↦ (⨅ i, (fun n ↦ g2_hat (n + 1)) i)) n := by
   intro n
   simp only
   apply Real.iInf_nonneg (f := (fun n ↦ g2_hat (n + 1)))
   intro i
   apply g2_hat_is_nonneg (i+1)

lemma g2_hat_le [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:∀ n : ℕ , (⨅ i, (fun n ↦ g2_hat (n + 1)) i) ≤ g2_hat (φ n.succ) := by
   intro n
   have := ciInf_le (g2_hat_bddbelow fullrank₁ fullrank₂) ((φ n.succ)-1)
   have h : φ n.succ > 0:= by
      calc _
         _ ≥ n + 1  := StrictMono.id_le (hphi_StrictMono fullrank₁ fullrank₂) (n + 1)
         _ > 0      :=by linarith
   have h2 : 1 ≤ φ n.succ := by linarith[h]
   have h1 : φ n.succ - 1 + 1 = φ n.succ := by apply Nat.sub_add_cancel h2
   rw[h1] at this
   exact this

lemma g2_hat_subseq_converge_zero
      [IsOrderedMonoid ℝ] [Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))] :
      Tendsto (fun n => g2_hat (φ n)) atTop (𝓝 0) := by
  simp only [g2_hat]
  obtain ⟨P, hP_pos, hQ_conv⟩ := Q_seq_converges_c2 fullrank₁ fullrank₂
  have hQ_sub : Tendsto (fun n => Q_seq_c2 (φ n)) atTop (𝓝 P) :=
    hQ_conv.comp (hphi_StrictMono fullrank₁ fullrank₂).tendsto_atTop
  have hg_sub : Tendsto (fun n => g2 (φ n)) atTop (𝓝 0) :=
    g2_subseq_converge_zero fullrank₁ fullrank₂
  have h_lim := Tendsto.div hg_sub hQ_sub (ne_of_gt hP_pos)
  rw [zero_div] at h_lim
  -- 使用 convert 解决 (f / g) 与 (fun n => f n / g n) 的句法差异
  convert h_lim using 2

lemma g2_hat_converge_zero''' [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
 Tendsto (fun _ : ℕ ↦ (⨅ i, (fun n ↦ g2_hat (n + 1)) i)) atTop (𝓝 0) := by
   apply squeeze_zero
   apply g2_hat_ge
   apply g2_hat_le
   have :=g2_hat_subseq_converge_zero fullrank₁ fullrank₂
   rw[← tendsto_add_atTop_iff_nat 1] at this
   exact this

lemma g2_hat_converge_zero'' [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
 Tendsto (fun _ : ℕ ↦ (⨅ i, (fun n ↦ g2_hat (n + 1)) i)) atTop (𝓝 (⨅ i, (fun n ↦ g2_hat (n + 1)) i)) := by
 apply tendsto_const_nhds

lemma g2_hat_converge_zero' [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      (⨅ i, (fun n ↦ g2_hat (n + 1)) i) = 0  := by
   apply tendsto_nhds_unique (g2_hat_converge_zero'' fullrank₁ fullrank₂)
   apply g2_hat_converge_zero'''

lemma g2_hat_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto g2_hat atTop (𝓝 0) := by
   rw[← tendsto_add_atTop_iff_nat 1]
   have := tendsto_atTop_ciInf (g2_hat_isMono fullrank₁ fullrank₂) (g2_hat_bddbelow fullrank₁ fullrank₂)
   rwa[← g2_hat_converge_zero']


-- 证明 g 全序列收敛到 0
-- 这是 Robbins-Siegmund 构造的最终结论
lemma g2_tendsto_zero
      [IsOrderedMonoid ℝ] [Condition_C2 admm admm_kkt]
      (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂)
      [s : Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂)] :
      Tendsto (fun n => g2 n) atTop (nhds 0) := by
  have h_ghat_zero := g2_hat_converge_zero fullrank₁ fullrank₂
  obtain ⟨P, hP⟩ := Q_seq_converges_c2 fullrank₁ fullrank₂
  have h_lim_mul := Tendsto.mul h_ghat_zero (hP.2)
  rw [zero_mul] at h_lim_mul
  have h_eq : (fun n => g2 n) = (fun n => g2_hat n * Q_seq_c2 n) := by
    funext n
    dsimp [g2_hat]
    have h_Q_pos : Q_seq_c2 n ≠ 0 := by
        apply ne_of_gt
        dsimp [Q_seq_c2]
        apply Finset.prod_pos
        intro n _
        linarith [sq_nonneg (θ_k n)]
    field_simp
  rw [h_eq]
  exact h_lim_mul

lemma A₂e₂_le_g2 (n : ℕ) [IsOrderedMonoid ℝ] [Condition_C2 admm admm_kkt]
      [Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      ‖A₂ (e₂ n)‖ ^ 2 ≤ (1 / τ) * g2 n := by
   have hτ : 0 < τ := admm.htau.1
   rw [mul_comm (1 / τ ) (g2 n)]
   field_simp
   rw [le_div_iff₀ (by linarith [hτ])]
   dsimp [g2]
   have h_ey_nonneg : 0 ≤ 1/ (ρₙ n)^2 * ‖ey n‖^2 := by
      have h2': 0 ≤ 1/ρₙ n^2 := by
         apply div_nonneg
         linarith
         linarith [sq_pos_of_pos (admm.hρₙ_pos n)]
      have h2'': 0 ≤ ‖ey n‖^2 := by exact sq_nonneg ‖ey n‖
      exact mul_nonneg h2' h2''
   have h_res_nonneg : 0 ≤ τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 := by
      apply mul_nonneg
      apply mul_nonneg
      exact (le_of_lt hτ)
      linarith [HWY_thm4_1_ineq]
      apply sq_nonneg _
   linarith [h_ey_nonneg, h_res_nonneg]

lemma A₂e₂_pow_converge_zero
      [IsOrderedMonoid ℝ] [Condition_C2 admm admm_kkt]
      [s : Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂)] :
      Tendsto (fun n => ‖A₂ (e₂ n)‖^2) atTop (nhds 0) := by
  -- 使用夹逼定理： 0 ≤ ‖A₂ (e₂ n)‖^2 ≤ (1/τ) * g2 n
  apply squeeze_zero
  · -- 证明下界：平方项非负
    intro n
    apply sq_nonneg
  · -- 证明上界：引用引理 A₂e₂_le_g2
    intro n
    apply A₂e₂_le_g2
  · -- 证明上界序列收敛到 0
    -- 因为 g2 n -> 0，常数 (1/τ) * g2 n 也 -> 0
    rw [← mul_zero (1 / τ)]
    apply Tendsto.const_mul
    apply g2_tendsto_zero fullrank₁ fullrank₂


lemma A₂e₂_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
   have : Tendsto (fun n => √((‖A₂ (e₂ n)‖)^2))  atTop (𝓝 √0) := by
      apply Tendsto.sqrt (A₂e₂_pow_converge_zero fullrank₁ fullrank₂)
   rw [Real.sqrt_zero] at this; simp [Real.sqrt_sq] at this; exact this

lemma A₁e₁_converge_zero
      [IsOrderedMonoid ℝ] [Condition_C2 admm admm_kkt]
      [s : Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂)] :
      Tendsto (fun n => ‖A₁ (e₁ n)‖) atTop (𝓝 0) := by
   let inst : Condition_C2 admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩)) :=
      { s with
        theta_square_summable := Condition_C2.theta_square_summable
        theta_square_summable' := Condition_C2.theta_square_summable'
        one_theta_square_multipliable' := Condition_C2.one_theta_square_multipliable'
        one_theta_square_multipliable := Condition_C2.one_theta_square_multipliable }
   haveI : Condition_C2 admm (admm_kkt_c2 fullrank₁ fullrank₂) := inst
   have h (n : ℕ) : ‖A₁ (e₁ n)‖ ≤ ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ := by
      let x := A₁ (e₁ n)
      let xx := A₂ (e₂ n)
      have h1 : ‖x‖ = ‖x + xx - xx‖ := by rw [← add_sub, sub_self, add_zero]
      have h2 : ‖x + xx - xx‖ ≤ ‖x + xx‖ + ‖xx‖ := by apply norm_sub_le
      rw [← h1] at h2
      linarith
   have h' (n : ℕ) : ‖‖A₁ (e₁ n)‖‖ ≤ ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ := by
      have : ‖‖A₁ (e₁ n)‖‖ = ‖A₁ (e₁ n)‖ := by simp only [norm_norm]
      rw [this]
      exact h n
   have h'' : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖) atTop (𝓝 (0 + 0)) := by
      have h_converge_zero₁ : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖) atTop (𝓝 0) := by
         apply converge_zero₁
      have h_A₂e₂_converge_zero : Tendsto (fun n => ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
         apply A₂e₂_converge_zero fullrank₁ fullrank₂
      apply Tendsto.add h_converge_zero₁ h_A₂e₂_converge_zero
   have h''' : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
      have : (0 : ℝ) = 0 + 0 := by norm_num
      rw [this]
      exact h''
   apply squeeze_zero_norm
   apply h'
   exact h'''

lemma A₁e₁_converge_zero' [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt]
      [Setting E₁ E₂ F admm admm_kkt]
      [Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖(A₁ ∘ e₁) n‖) atTop (𝓝 0) := by
   have : (fun n => ‖A₁ (e₁ n)‖) = (fun n => ‖(A₁ ∘ e₁) n‖) := by simp only [Function.comp_apply]
   rw [← this]
   apply A₁e₁_converge_zero

lemma CA₁e₁_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt]
      [Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]
      (C : ℝ) :
      Tendsto (fun n => C * ‖A₁ (e₁ n)‖) atTop (𝓝 0) := by
   have : Tendsto (fun n => ‖A₁ (e₁ n)‖) atTop (𝓝 0) := by apply A₁e₁_converge_zero
   have h : C * 0 = 0 := by simp only [mul_zero]
   rw[← h]; apply Tendsto.const_mul C this

lemma CA₂e₂_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))](C : ℝ) :
      Tendsto (fun n => C * ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
   have : Tendsto (fun n => ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by apply A₂e₂_converge_zero
   have h : C * 0 = 0 := by simp only [mul_zero]
   rw[← h]; apply Tendsto.const_mul C this

lemma e₁_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto e₁ atTop (𝓝 0) := by
   have : ∃ C > 0, ∀ n : ℕ, ‖e₁ n‖ ≤ C * ‖A₁ (e₁ n)‖ := open_mapping_e₁ fullrank₁
   obtain ⟨C, _, hC⟩ := this
   apply squeeze_zero_norm; intro n; exact hC n; apply CA₁e₁_converge_zero


lemma e₂_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto e₂ atTop (𝓝 0) := by
   have : ∃ C > 0, ∀ n : ℕ, ‖e₂ n‖ ≤ C * ‖A₂ (e₂ n)‖ := open_mapping_e₂ fullrank₂
   obtain ⟨C, _, hC⟩ := this
   apply squeeze_zero_norm; intro n; exact hC n; apply CA₂e₂_converge_zero


lemma ey_sq_le_g
      [IsOrderedMonoid ℝ] [Condition_C2 admm admm_kkt]
      (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂)
      [s : Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂)]
      (n : ℕ) :
      ‖ey n‖ ^ 2 ≤ ρₙ n^2 * g2 n := by
   -- 展开 g2 的定义
   dsimp [g2]
   -- 计算 ρₙ n^2 * g2 n = ‖ey n‖^2 + ρₙ n^2 * (τ * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2)
   have h1 : ‖ey n‖^2 = ρₙ n^2 * (1 / ρₙ n^2 * ‖ey n‖^2) := by
      have h_ne_zero : ρₙ n^2 ≠ 0 := ne_of_gt (sq_pos_of_pos (admm.hρₙ_pos n))
      have h_ne_zero' : ρₙ n ≠ 0 := ne_of_gt (admm.hρₙ_pos n)
      field_simp [h_ne_zero, h_ne_zero']
   have h2 : 0 ≤ τ * ‖A₂ (e₂ n)‖^2 := by
      apply mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg _)
   have h3 : 0 ≤ τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
      apply mul_nonneg
      apply mul_nonneg (le_of_lt admm.htau.1)
      linarith [HWY_thm4_1_ineq]
      apply sq_nonneg
   have h4 : 0 ≤ ρₙ n^2 * (τ * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) := by
      apply mul_nonneg (sq_nonneg _)
      linarith [h2, h3]
   calc ‖ey n‖^2
      = ρₙ n^2 * (1 / ρₙ n^2 * ‖ey n‖^2) := h1
      _ ≤ ρₙ n^2 * (1 / ρₙ n^2 * ‖ey n‖^2) + ρₙ n^2 * (τ * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) := by linarith
      _ = ρₙ n^2 * g2 n := by unfold g2; ring_nf


lemma ey_sqnrm_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt]
      [Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖ey n‖^2) atTop (𝓝 0) := by
   -- 1. 获取 ρₙ 的上界 BU
   obtain ⟨BU, hBU⟩ := admm.rho_upper_bound
   -- 2. 使用夹逼定理 squeeze_zero
   -- squeeze_zero 需要三个参数:
   -- (1) ∀ n, 0 ≤ f n (下界)
   -- (2) ∀ n, f n ≤ g n (上界)
   -- (3) Tendsto g atTop (𝓝 0) (上界收敛)
   apply squeeze_zero
   · -- 分支 1: 证明非负性
     intro n
     exact sq_nonneg _
   · -- 分支 2: 证明上界 ‖ey n‖^2 ≤ BU^2 * g2 n
     intro n
     -- 引入之前的引理：‖ey n‖^2 ≤ ρₙ^2 * g2 n
     have h_local := ey_sq_le_g fullrank₁ fullrank₂ n
     -- 使用 calc 模式或 gcongr 进行放缩
     calc ‖ey n‖^2
       _ ≤ ρₙ n^2 * g2 n := h_local
       _ ≤ BU^2 * g2 n   := by
         -- 利用 gcongr 自动处理单调性
         gcongr
         · apply hBU.2 n -- ρₙ ≤ BU
   · -- 分支 3: 证明上界收敛到 0
     -- 目标: Tendsto (fun n => BU^2 * g2 n) atTop (𝓝 0)
     rw [← mul_zero (BU^2)] -- 将 0 重写为 BU^2 * 0
     apply Filter.Tendsto.const_mul -- 应用常数乘法极限规则
     apply g2_tendsto_zero fullrank₁ fullrank₂ -- 应用 g2 收敛到 0 的引理


lemma ey_nrm_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto (fun n => ‖ey n‖)  atTop (𝓝 0) := by
   rw [← Real.sqrt_zero]
   have : (fun n => ‖ey n‖) = (fun n => √(‖ey n‖^2)) := by funext n; simp [Real.sqrt_sq]
   rw [this]
   apply Filter.Tendsto.sqrt (ey_sqnrm_converge_zero fullrank₁ fullrank₂)

lemma ey_converge_zero [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto ey atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2
   apply ey_nrm_converge_zero

--lim_{ n → ∞} x_n - x = 0 =>  lim_{ n → ∞} x_n  = x
lemma x₁_converge [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto x₁ atTop (𝓝 x₁'') := by
   have : e₁ = (fun n => (x₁ n) - x₁''):= rfl
   have h := e₁_converge_zero fullrank₁ fullrank₂
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

lemma x₂_converge [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto x₂ atTop (𝓝 x₂'') := by
   have : e₂ = (fun n => (x₂ n) - x₂''):= rfl
   have h := e₂_converge_zero fullrank₁ fullrank₂
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

lemma y_converge [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      Tendsto y atTop (𝓝 y'') := by
   have : ey = (fun n => (y n) - y''):= rfl
   have h := ey_converge_zero fullrank₁ fullrank₂
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

--Adaptive ADMM of condition C1 convergence theorem
theorem adaptive_admm_convergence [IsOrderedMonoid ℝ][Condition_C2 admm admm_kkt][Setting E₁ E₂ F admm (admm_kkt_c2 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩))]:
      ∃ ( _x₁   : E₁) ( _x₂ : E₂) ( _y : F) , Convex_KKT _x₁ _x₂ _y admm.toOptProblem
      ∧ ( Tendsto x₁ atTop (𝓝 _x₁)∧ Tendsto x₂ atTop (𝓝 _x₂)∧ Tendsto y atTop (𝓝 _y)) :=
   ⟨x₁'',x₂'',y'',Iskktpair fullrank₁ fullrank₂ ,
   x₁_converge fullrank₁ fullrank₂ ,x₂_converge fullrank₁ fullrank₂,
   y_converge fullrank₁ fullrank₂⟩

end AdaptiveADMM_Convergence_Proof
